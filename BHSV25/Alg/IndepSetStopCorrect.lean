module

public import BHSV25.Alg.IndepSetStop

/-!
# Theorem 7.20: the analysis of the algorithm that finds the number of rounds

The guarantee of `BHSV25.Alg.indepAlgU` (`BHSV25.Alg.roundsU_le`,
`BHSV25.Alg.card_indepAlgU_ge`), for the gap `g = max(r / s, 1 / (4 n⁴))` and the threshold
`ψ = 1 - (1 - 1/β) g / 2` of `BHSV25.Alg.thrF`:

* the eigenvalues above `-θ'`, for `θ' = 1 - g ≥ min(λ, 1 - 1/(4 n⁴))`, are noise: the filter
  makes them at most `ℓ = (1 - g/2)^E`, and at most `t` eigenvalues are at most `-θ'`, as in
  `BHSV25.Alg.card_indepAlgGS_ge`;
* the target is the projection onto the eigenvectors with eigenvalue at most `-θ`, for
  `θ = 1 - (1 - c'') g`, where the filter is at least `h = (1 - (1 - c'') g / 2)^E`;
* the threshold lies between: `ψ^E ≥ 2^(n+1) ℓ` and `√n ψ^E / h ≤ 2 / K`, as `ψ` is `c'' g / 10`
  away from both and `E g ≥ a n / 4` (`BHSV25.Alg.noise_le_thr`, `BHSV25.Alg.thr_le_target`).

So the stopping round is at most `t`, and the net at the stopping round has a vector within
`4 / K` of the target (`BHSV25.Net.exists_cand_near_stop`); the rest is the proof of
`BHSV25.Alg.card_indepAlgGS_ge`, with `1 - θ ≥ (1 - c'')² (1 - λ)`.
-/

@[expose] public section

namespace BHSV25.Alg

open Matrix

/-! ### The threshold -/

/-- A ratio bounded away from `1`: if `x + κ ≤ y ≤ 1` with `x, κ ≥ 0`, then
`x^E ≤ y^E exp(-κ E)`. -/
theorem pow_le_mul_exp {x y κ : ℝ} (hx : 0 ≤ x) (hy1 : y ≤ 1) (hκ : 0 ≤ κ) (hxy : x + κ ≤ y)
    (E : ℕ) : x ^ E ≤ y ^ E * Real.exp (-(κ * E)) := by
  have hy0 : 0 ≤ y := by linarith only [hx, hκ, hxy]
  have h1 : x ≤ y * Real.exp (-κ) := by
    have h2 : 1 - κ ≤ Real.exp (-κ) := by linarith only [Real.add_one_le_exp (-κ)]
    have h3 : y * (1 - κ) ≤ y * Real.exp (-κ) := mul_le_mul_of_nonneg_left h2 hy0
    have h4 : κ * y ≤ κ := mul_le_of_le_one_right hκ hy1
    linarith only [hxy, h3, h4]
  calc x ^ E ≤ (y * Real.exp (-κ)) ^ E := pow_le_pow_left₀ hx h1 E
    _ = y ^ E * Real.exp (-(κ * E)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring

/-- The exponent: `(3 + K/2) n ≤ (c'' g / 10) a n⁵` for `g ≥ 1/(4 n⁴)` and
`a ≥ 40 (3 + K/2) / c''`. -/
theorem stopB_exponent {n K a : ℕ} (hn : 0 < n) {cc g : ℝ} (hcc0 : 0 < cc)
    (hg0 : 1 / (4 * (n : ℝ) ^ 4) ≤ g) (ha : 40 * (3 + K / 2 : ℝ) / cc ≤ a) :
    (3 + K / 2 : ℝ) * n ≤ cc * g / 10 * ((a * n ^ 5 : ℕ) : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 1 ≤ 4 * (n : ℝ) ^ 4 * g := by
    rw [div_le_iff₀ (by positivity)] at hg0
    linarith only [hg0]
  have h2 : 40 * (3 + K / 2 : ℝ) ≤ cc * a := by
    rw [div_le_iff₀ hcc0] at ha
    linarith only [ha]
  have h3 : 40 * (3 + K / 2 : ℝ) * 1 ≤ cc * a * (4 * (n : ℝ) ^ 4 * g) :=
    mul_le_mul h2 h1 zero_le_one (by positivity)
  have h4 := mul_le_mul_of_nonneg_right h3 hn'.le
  have e : cc * g / 10 * ((a * n ^ 5 : ℕ) : ℝ) = cc * a * (4 * (n : ℝ) ^ 4 * g) * n / 40 := by
    push_cast
    ring
  rw [e]
  linarith only [h4]

/-- `2^(n+1) exp(-κ) ≤ 1` for `κ ≥ 3 n`, `n ≥ 1`. -/
theorem stopB_two_pow_mul_exp_le {n : ℕ} (hn : 0 < n) {κ : ℝ} (hκ : 3 * (n : ℝ) ≤ κ) :
    (2 : ℝ) ^ (n + 1) * Real.exp (-κ) ≤ 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (2 : ℝ) ^ (n + 1) ≤ Real.exp (n + 1) := by
    have h := Real.add_one_le_exp 1
    calc (2 : ℝ) ^ (n + 1) ≤ Real.exp 1 ^ (n + 1) :=
          pow_le_pow_left₀ (by norm_num) (by linarith only [h]) _
      _ = Real.exp (n + 1) := by rw [← Real.exp_nat_mul, mul_one]; push_cast; ring_nf
  calc (2 : ℝ) ^ (n + 1) * Real.exp (-κ) ≤ Real.exp (n + 1) * Real.exp (-κ) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (n + 1 - κ) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp 0 := Real.exp_le_exp.2 (by linarith only [hn', hκ])
    _ = 1 := Real.exp_zero

/-- **The noise is below the threshold**: for `n ≥ 1`, `1/(4 n⁴) ≤ g ≤ 1`, `c''/5 ≤ 1/β` and
`a ≥ 40 (3 + K/2) / c''`, `2^(n+1) (1 - g/2)^(a n⁵) ≤ ψ^(a n⁵)` for
`ψ = 1 - (1 - 1/β) g / 2`. -/
theorem noise_le_thr {n K a β : ℕ} (hn : 0 < n) {cc g : ℝ} (hcc0 : 0 < cc)
    (hg0 : 1 / (4 * (n : ℝ) ^ 4) ≤ g) (hg1 : g ≤ 1) (hβ : cc / 5 ≤ 1 / (β : ℝ))
    (hβ1 : 1 ≤ β) (ha : 40 * (3 + K / 2 : ℝ) / cc ≤ a) :
    2 ^ (n + 1) * (1 - g / 2) ^ (a * n ^ 5) ≤ (1 - (1 - 1 / (β : ℝ)) * g / 2) ^ (a * n ^ 5) := by
  have hβ' : (1 : ℝ) ≤ β := by exact_mod_cast hβ1
  have hb1 : 1 / (β : ℝ) ≤ 1 := by rw [div_le_one (by linarith only [hβ'])]; exact hβ'
  have hg0' : 0 < g := lt_of_lt_of_le (by positivity) hg0
  have hbg : 0 ≤ (1 - 1 / (β : ℝ)) * g := mul_nonneg (by linarith only [hb1]) hg0'.le
  have hbg' : cc / 5 * g ≤ 1 / (β : ℝ) * g := mul_le_mul_of_nonneg_right hβ hg0'.le
  have hmain := pow_le_mul_exp (x := 1 - g / 2) (y := 1 - (1 - 1 / (β : ℝ)) * g / 2)
    (κ := cc * g / 10) (by linarith only [hg1]) (by linarith only [hbg])
    (by positivity) (by linarith only [hbg']) (a * n ^ 5)
  have hK : (0 : ℝ) ≤ K / 2 := by positivity
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hexp := stopB_exponent (K := K) hn hcc0 hg0 ha
  have h2 := stopB_two_pow_mul_exp_le hn (κ := cc * g / 10 * ((a * n ^ 5 : ℕ) : ℝ))
    (by nlinarith only [hexp, hK, hn'])
  have hbg0 : 0 ≤ 1 / (β : ℝ) * g := by positivity
  have hψ0 : 0 ≤ (1 - (1 - 1 / (β : ℝ)) * g / 2) ^ (a * n ^ 5) :=
    pow_nonneg (by linarith only [hbg0, hg1]) _
  calc 2 ^ (n + 1) * (1 - g / 2) ^ (a * n ^ 5)
      ≤ 2 ^ (n + 1) * ((1 - (1 - 1 / (β : ℝ)) * g / 2) ^ (a * n ^ 5) *
          Real.exp (-(cc * g / 10 * ((a * n ^ 5 : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (1 - (1 - 1 / (β : ℝ)) * g / 2) ^ (a * n ^ 5) *
          (2 ^ (n + 1) * Real.exp (-(cc * g / 10 * ((a * n ^ 5 : ℕ) : ℝ)))) := by ring
    _ ≤ (1 - (1 - 1 / (β : ℝ)) * g / 2) ^ (a * n ^ 5) * 1 := mul_le_mul_of_nonneg_left h2 hψ0
    _ = _ := mul_one _

/-- **The threshold is below the target**: for `n ≥ 1`, `1/(4 n⁴) ≤ g ≤ 1`, `1/β ≤ c''/4` and
`a ≥ 40 (3 + K/2) / c''`, `√n ψ^(a n⁵) / (1 - (1 - c'') g / 2)^(a n⁵) ≤ 2 / K`. -/
theorem thr_le_target {n K a β : ℕ} (hn : 0 < n) (hK : 0 < K) {cc g : ℝ} (hcc0 : 0 < cc)
    (hcc1 : cc ≤ 1) (hg0 : 1 / (4 * (n : ℝ) ^ 4) ≤ g) (hg1 : g ≤ 1)
    (hβ : 1 / (β : ℝ) ≤ cc / 4) (ha : 40 * (3 + K / 2 : ℝ) / cc ≤ a) :
    Real.sqrt n * (1 - (1 - 1 / (β : ℝ)) * g / 2) ^ (a * n ^ 5) /
      (1 - (1 - cc) * g / 2) ^ (a * n ^ 5) ≤ 2 / K := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hb0 : 0 ≤ 1 / (β : ℝ) := by positivity
  have hg0' : 0 < g := lt_of_lt_of_le (by positivity) hg0
  have hbg : 1 / (β : ℝ) * g ≤ cc / 4 * g := mul_le_mul_of_nonneg_right hβ hg0'.le
  have hbg0 : 0 ≤ 1 / (β : ℝ) * g := mul_nonneg hb0 hg0'.le
  have hcg : 0 ≤ cc * g := mul_nonneg hcc0.le hg0'.le
  have hcg1 : cc * g ≤ g := by nlinarith only [hcc1, hg0']
  set E := a * n ^ 5 with hE
  have hh0 : 0 < (1 - (1 - cc) * g / 2) ^ E := pow_pos (by linarith only [hcg, hg1]) E
  have hmain := pow_le_mul_exp (x := 1 - (1 - 1 / (β : ℝ)) * g / 2)
    (y := 1 - (1 - cc) * g / 2) (κ := cc * g / 10) (by linarith only [hbg0, hg1])
    (by linarith only [hcg1]) (by positivity) (by linarith only [hbg, hcg]) E
  have hexp := stopB_exponent (K := K) hn hcc0 hg0 ha
  have hsq : Real.sqrt n ≤ Real.exp n := by
    have h1 : Real.sqrt n ≤ n + 1 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith only [hn']
    linarith only [h1, Real.add_one_le_exp (n : ℝ)]
  have hK2 : (K : ℝ) / 2 ≤ K / 2 * n := by nlinarith only [hn', hK']
  have herr : Real.sqrt n * Real.exp (-(cc * g / 10 * (E : ℝ))) ≤ 2 / K := by
    calc Real.sqrt n * Real.exp (-(cc * g / 10 * (E : ℝ)))
        ≤ Real.exp n * Real.exp (-(cc * g / 10 * (E : ℝ))) :=
          mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
      _ = Real.exp (n - cc * g / 10 * (E : ℝ)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(K / 2)) := Real.exp_le_exp.2 (by linarith only [hexp, hK2, hn'])
      _ ≤ 2 / K := exp_neg_half_le hK'
  rw [div_le_iff₀ hh0]
  calc Real.sqrt n * (1 - (1 - 1 / (β : ℝ)) * g / 2) ^ E
      ≤ Real.sqrt n * ((1 - (1 - cc) * g / 2) ^ E * Real.exp (-(cc * g / 10 * (E : ℝ)))) :=
        mul_le_mul_of_nonneg_left hmain (Real.sqrt_nonneg _)
    _ = (Real.sqrt n * Real.exp (-(cc * g / 10 * (E : ℝ)))) * (1 - (1 - cc) * g / 2) ^ E := by
        ring
    _ ≤ 2 / K * (1 - (1 - cc) * g / 2) ^ E := mul_le_mul_of_nonneg_right herr hh0.le

/-! ### The gap and the threshold as real numbers -/

/-- `β ≥ 1` when `c''/5 ≤ 1/β` for `c'' > 0`. -/
theorem stopB_one_le {cc : ℝ} (hcc0 : 0 < cc) {β : ℕ} (hβ : cc / 5 ≤ 1 / (β : ℝ)) : 1 ≤ β := by
  rcases Nat.eq_zero_or_pos β with h | h
  · subst h
    have : (0 : ℝ) < cc / 5 := by positivity
    simp only [Nat.cast_zero, div_zero] at hβ
    linarith only [this, hβ]
  · exact h

/-- **The gap** `g = max(r / s, 1/(4 n⁴))` of `BHSV25.Alg.gapF`, for `n ≥ 1` and `0 < r ≤ s`: its
denominator is positive and at least its numerator, `1/(4 n⁴) ≤ g ≤ 1`, `r / s ≤ g`, and `g` is
`r / s` or `1/(4 n⁴)`. -/
theorem stopB_gap {r s n : ℕ} (hn : 0 < n) (hr : 0 < r) (hrs : r ≤ s) :
    0 < (gapF r s n).2 ∧ (gapF r s n).1 ≤ (gapF r s n).2 ∧
      1 / (4 * (n : ℝ) ^ 4) ≤ ((gapF r s n).1 : ℝ) / (gapF r s n).2 ∧
      ((gapF r s n).1 : ℝ) / (gapF r s n).2 ≤ 1 ∧
      (r : ℝ) / s ≤ ((gapF r s n).1 : ℝ) / (gapF r s n).2 ∧
      (((gapF r s n).1 : ℝ) / (gapF r s n).2 = r / s ∨
        ((gapF r s n).1 : ℝ) / (gapF r s n).2 = 1 / (4 * (n : ℝ) ^ 4)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn4 : (1 : ℝ) ≤ 4 * (n : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn'
    linarith only [this]
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  unfold gapF
  split_ifs with h
  · have h' : (s : ℝ) ≤ 4 * (n : ℝ) ^ 4 * r := by exact_mod_cast h
    refine ⟨hs, hrs, ?_, ?_, le_rfl, Or.inl rfl⟩
    · rw [div_le_div_iff₀ (by positivity) hs']
      linarith only [h']
    · rw [div_le_one hs']
      exact_mod_cast hrs
  · have h' : 4 * (n : ℝ) ^ 4 * r ≤ s := by exact_mod_cast (not_le.1 h).le
    refine ⟨by positivity, ?_, ?_, ?_, ?_, Or.inr ?_⟩
    · change 1 ≤ 4 * n ^ 4
      exact_mod_cast hn4
    · push_cast
      exact le_rfl
    · push_cast
      rw [div_le_one (by positivity)]
      exact hn4
    · push_cast
      rw [div_le_div_iff₀ hs' (by positivity)]
      linarith only [h']
    · push_cast
      rfl

/-- **The threshold** of `BHSV25.Alg.thrF` is `ψ = 1 - (1 - 1/β) g / 2` for the gap `g`, with a
positive denominator, for `β, n ≥ 1` and `0 < r ≤ s`. -/
theorem stopB_thr {β r s n : ℕ} (hβ : 1 ≤ β) (hn : 0 < n) (hr : 0 < r) (hrs : r ≤ s) :
    0 < (thrF β r s n).2 ∧ ((thrF β r s n).1 : ℝ) / (thrF β r s n).2 =
      1 - (1 - 1 / (β : ℝ)) * (((gapF r s n).1 : ℝ) / (gapF r s n).2) / 2 := by
  obtain ⟨hg2, hg12, -⟩ := stopB_gap hn hr hrs
  obtain ⟨g₁, hg₁⟩ : ∃ x, x = (gapF r s n).1 := ⟨_, rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ x, x = (gapF r s n).2 := ⟨_, rfl⟩
  rw [← hg₁, ← hg₂] at hg12 ⊢
  rw [← hg₂] at hg2
  have hle : (β - 1) * g₁ ≤ 2 * β * g₂ := by
    have h1 : (β - 1) * g₁ ≤ β * g₂ := Nat.mul_le_mul (Nat.sub_le _ _) hg12
    have h2 : β * g₂ ≤ 2 * β * g₂ := by
      rw [mul_assoc 2]
      exact Nat.le_mul_of_pos_left _ two_pos
    exact h1.trans h2
  have hden : 0 < 2 * β * g₂ := by positivity
  refine ⟨?_, ?_⟩
  · simp only [thrF, ← hg₁, ← hg₂]
    exact hden
  · have hβ' : (β : ℝ) ≠ 0 := by positivity
    have hg2' : (g₂ : ℝ) ≠ 0 := by positivity
    simp only [thrF, ← hg₁, ← hg₂]
    rw [Nat.cast_sub hle]
    push_cast [Nat.cast_sub hβ]
    field_simp

/-! ### The number of rounds on a graph -/

/-- `a ≥ 1` when `a ≥ 40 (3 + K/2) / c''` for `c'' > 0`. -/
theorem stopB_a_pos {cc : ℝ} (hcc0 : 0 < cc) {a K : ℕ} (ha : 40 * (3 + K / 2 : ℝ) / cc ≤ a) :
    0 < a := by
  have h : (0 : ℝ) < a := lt_of_lt_of_le (by positivity) ha
  exact_mod_cast h

/-- The number of rounds is at most the number of vertices. -/
theorem stopB_roundsU_le_numV (p : UPar) (x : ℕ × List Bool) : roundsU p x ≤ numV x := by
  unfold roundsU Net.stopZ
  exact List.countP_le_length.trans (by rw [List.length_range])

/-- **The number of rounds on a graph** with vertices of degree `d`: the stopping round on the
filter `Q = (d I - A)^E`, `E = a n⁵`. -/
theorem stopB_roundsU_eq (a K β r s : ℕ) (G : Graph) {d : ℕ}
    (hdeg : Net.deg G.1 (adjTable G) = d) :
    roundsU (a, K, β, r, s) (G.1, adjTable G) =
      Net.stopZ G.1
        (Net.gramRows G.1 (Net.powL G.1 (Net.baseMat true G.1 d (adjTable G)) (a * G.1 ^ 5)))
        (((thrF β r s G.1).2 ^ (2 * (a * G.1 ^ 5)) : ℕ) : ℤ)
        (((2 * d * (thrF β r s G.1).1) ^ (2 * (a * G.1 ^ 5)) : ℕ) : ℤ) := by
  simp only [roundsU, Net.filtQ, numV_graph, Net.numV_graph, hdeg]

open Classical in
/-- **No edges, no rounds**: on a graph with vertices of degree `0`, for `a ≥ 1` and a positive
denominator of the threshold, the number of rounds is `0`: the filter is `0`, so the test holds
at round `0`. -/
theorem stopB_roundsU_deg_zero (a K β r s : ℕ) (G : Graph) (hd : G.2.IsRegularOfDegree 0)
    (hn : 0 < G.1) (ha : 0 < a) (hden : 0 < (thrF β r s G.1).2) :
    roundsU (a, K, β, r, s) (G.1, adjTable G) = 0 := by
  have hdeg : Net.deg G.1 (adjTable G) = 0 := by rw [Net.deg_graph G hn]; exact hd _
  rw [stopB_roundsU_eq a K β r s G hdeg]
  obtain ⟨E, hE⟩ : ∃ E, E = a * G.1 ^ 5 := ⟨_, rfl⟩
  have hE0 : E ≠ 0 := by rw [hE]; positivity
  rw [← hE]
  set Q := Net.powL G.1 (Net.baseMat true G.1 0 (adjTable G)) E with hQ
  -- the filter is `0`
  have hM : Net.toMat G.1 (Net.baseMat true G.1 0 (adjTable G)) = 0 := by
    funext u v
    rw [Net.toMat_baseMat]
    have hadj : ¬ G.2.Adj u v := by
      intro hadj
      have h := hd u
      rw [SimpleGraph.degree, Finset.card_eq_zero] at h
      have hv : v ∈ G.2.neighborFinset u := (SimpleGraph.mem_neighborFinset _ _ _).2 hadj
      rw [h] at hv
      exact Finset.notMem_empty v hv
    simp [Net.entry, Net.adjB_graph, hadj]
  have hcol : ∀ v < G.1, Net.colZ G.1 Q v = 0 := by
    intro v hv
    funext u
    have h : Cslib.rowEntry Q v u = Net.toMat G.1 Q ⟨v, hv⟩ u := rfl
    have h2 : Net.toMat G.1 Q = 0 := by rw [hQ, Net.toMat_powL, hM, zero_pow hE0]
    simp only [Net.colZ, Pi.zero_apply, h, h2, Matrix.zero_apply, Int.cast_zero]
  have hX : (0 : ℤ) < (((thrF β r s G.1).2 ^ (2 * E) : ℕ) : ℤ) := by positivity
  have hG := Net.rowEntry_gramRows (n := G.1) Q (by rw [hQ, Net.length_powL])
  have hok : Net.okZ G.1 (Net.gramRows G.1 Q) (((thrF β r s G.1).2 ^ (2 * E) : ℕ) : ℤ)
      (((2 * 0 * (thrF β r s G.1).1) ^ (2 * E) : ℕ) : ℤ)
      (Net.selOf G.1 0 (Net.gramRows G.1 Q)) = true := by
    rw [Net.okZ_iff _ (Net.colZ G.1 Q) hG hX]
    intro v hv
    have hr0 : Net.resid (Net.colsL (Net.colZ G.1 Q) (Net.selOf G.1 0 (Net.gramRows G.1 Q)))
        0 = 0 := (Net.residL _).map_zero
    rw [hcol v hv, hr0]
    simp [hE0]
  exact Nat.le_zero.1 (Net.stopZ_spec _ (Net.colZ G.1 Q) hG hX _ (Nat.zero_le _) hok).2

/-! ### The filter and the test on a graph -/

open Classical in
/-- The filter `c Q`, for `c = (2d)^(-E)` and `Q = (d I - A)^E`, acts on the eigenbasis by
`((1 - μᵢ)/2)^E`. -/
theorem stopB_hP (G : Graph) {d : ℕ} (hd : G.2.IsRegularOfDegree d) (hd0 : 0 < d) (E : ℕ)
    (i : Fin G.1) (x : Fin G.1 → ℝ) :
    Spectral.coeff G.normAdj_isHermitian i
        ((((Net.denBase (Net.bParams true) d : ℝ)⁻¹ ^ E) • Matrix.of fun u v : Fin G.1 ↦
          (Cslib.rowEntry (Net.powL G.1 (Net.baseMat true G.1 d (adjTable G)) E) u v : ℝ)) *ᵥ
          x) =
      ((1 - G.eig i) / 2) ^ E * Spectral.coeff G.normAdj_isHermitian i x := by
  have hbase : (Net.denBase (Net.bParams true) d : ℝ)⁻¹ • (Net.toMat G.1 (Net.baseMat true G.1 d
      (adjTable G))).map (Int.castRingHom ℝ) = (1 / 2 : ℝ) • (1 - G.normAdj) :=
    Net.bottom_base (Net.bParams true) rfl G hd hd0
  rw [Net.filter_eq, hbase]
  exact Net.coeff_pow_mulVec _ (Net.coeff_halfSub G i) E x

/-- **The test of the threshold**: `c² Y = (ψ^E)² X` for `c = (2d)^(-E)`, `X = den^(2E)`,
`Y = (2 d num)^(2E)` and `ψ = num / den`. -/
theorem stopB_test {d num den E : ℕ} (hd0 : d ≠ 0) (hden : 0 < den) {ψ : ℝ}
    (hψ : (num : ℝ) / den = ψ) :
    ((Net.denBase (Net.bParams true) d : ℝ)⁻¹ ^ E) ^ 2 *
        ((((2 * d * num) ^ (2 * E) : ℕ) : ℤ) : ℝ) =
      (ψ ^ E) ^ 2 * (((den ^ (2 * E) : ℕ) : ℤ) : ℝ) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hden' : (den : ℝ) ≠ 0 := by positivity
  have h2d : ((Net.denBase (Net.bParams true) d : ℕ) : ℝ) = 2 * d := by
    simp only [Net.denBase, Net.bParams, ite_true]
    push_cast
    ring
  rw [← hψ, h2d]
  push_cast
  rw [← pow_mul, ← pow_mul, mul_comm E 2, ← mul_pow, ← mul_pow]
  congr 1
  field_simp

open Classical in
/-- **Few eigenvalues at most `-(1 - g)`**: at most `t` if `g ≤ 1 - λ` or `g = 1/(4 n⁴)`, on a
regular graph with at most `t` eigenvalues at most `-λ`, as no eigenvalue lies in
`(-1, -1 + 1/(2 n⁴))`. -/
theorem stopB_card_le (G : Graph) (hreg : G.IsRegular) {lam : ℝ} (hl1 : lam < 1) {t : ℕ}
    (ht : (Finset.univ.filter fun i ↦ G.eig i ≤ -lam).card ≤ t) {g : ℝ}
    (hg : g ≤ 1 - lam ∨ g = 1 / (4 * (G.1 : ℝ) ^ 4)) :
    (Finset.univ.filter fun i ↦ G.eig i ≤ -(1 - g)).card ≤ t := by
  refine (Finset.card_le_card fun i hi ↦ ?_).trans ht
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨hi.1, ?_⟩
  rcases hg with h | h
  · linarith only [hi.2, h]
  · rcases eig_eq_neg_one_or_ge G hreg i with he | he
    · rw [he]
      linarith only [hl1]
    · exfalso
      have hn : (0 : ℝ) < G.1 := by exact_mod_cast Fin.pos i
      have h4 : 0 < 1 / (4 * (G.1 : ℝ) ^ 4) := by positivity
      have e : 1 / (2 * (G.1 : ℝ) ^ 4) = 2 * (1 / (4 * (G.1 : ℝ) ^ 4)) := by
        field_simp
        ring
      rw [e] at he
      rw [h] at hi
      linarith only [hi.2, he, h4]

/-- The grid's error: `2 √T / ((⌊√T⌋ + 1) K) ≤ 2 / K`. -/
theorem stopB_grid (T : ℕ) {K : ℕ} (hK : 0 < K) :
    2 * Real.sqrt T / (((Nat.sqrt T + 1) * K : ℕ) : ℝ) ≤ 2 / K := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hs : Real.sqrt T ≤ (Nat.sqrt T + 1 : ℕ) := by
    push_cast
    exact (Real.real_sqrt_lt_nat_sqrt_succ).le
  rw [Nat.cast_mul, div_le_div_iff₀ (by positivity) hK']
  have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * K)
  linarith only [this]

open Classical in
/-- **The net at the stopping round** on a `d`-regular graph, `d ≥ 1`, with at most `t`
eigenvalues at most `-λ`, for the parameters of `BHSV25.Alg.roundsU_le`: the stopping round `T`
is at most `t`, and with a budget `B` that covers the ball of radius `N = (⌊√T⌋ + 1) K`, the net
contains, for every vector `w` of length at most `1` in the span of the eigenvectors with
eigenvalue at most `-θ`, `θ = 1 - (1 - c'') g`, a vector within `4 / K`. -/
theorem stopB_net (G : Graph) {d : ℕ} (hd : G.2.IsRegularOfDegree d) (hd0 : d ≠ 0)
    (hn : 0 < G.1) {lam : ℝ} (hl1 : lam < 1) {t : ℕ}
    (ht : (Finset.univ.filter fun i ↦ G.eig i ≤ -lam).card ≤ t) {cc : ℝ} (hcc0 : 0 < cc)
    (hcc1 : cc ≤ 1) {a K β r s : ℕ} (hK : 0 < K) (ha : 40 * (3 + K / 2 : ℝ) / cc ≤ a)
    (hβ1 : cc / 5 ≤ 1 / (β : ℝ)) (hβ2 : 1 / (β : ℝ) ≤ cc / 4) (hr : 0 < r) (hrs : r ≤ s)
    (hhi : (r : ℝ) / s ≤ 1 - lam) {T : ℕ}
    (hT : roundsU (a, K, β, r, s) (G.1, adjTable G) = T) :
    T ≤ t ∧ ∀ B : ℕ, Net.BallBudget ((Nat.sqrt T + 1) * K) T B → ∀ w : Fin G.1 → ℝ,
      w ⬝ᵥ w ≤ 1 →
      G.InEigSpan (· ≤ -(1 - (1 - cc) * (((gapF r s G.1).1 : ℝ) / (gapF r s G.1).2))) w →
      ∃ c ∈ Net.netGS true (a * G.1 ^ 5) T ((Nat.sqrt T + 1) * K) B (G.1, adjTable G),
        Real.sqrt ((Net.ratVec G.1 c - w) ⬝ᵥ (Net.ratVec G.1 c - w)) ≤ 4 / K := by
  have hβ0 : 1 ≤ β := stopB_one_le hcc0 hβ1
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  -- the gap and the threshold
  obtain ⟨-, -, hg0, hg1, -, hgcase⟩ := stopB_gap hn hr hrs
  obtain ⟨hden, hψ⟩ := stopB_thr hβ0 hn hr hrs
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = ((gapF r s G.1).1 : ℝ) / (gapF r s G.1).2 := ⟨_, rfl⟩
  rw [← hg] at hg0 hg1 hgcase hψ ⊢
  have hg0' : 0 < g := lt_of_lt_of_le (by positivity) hg0
  have hdeg : Net.deg G.1 (adjTable G) = d := by rw [Net.deg_graph G hn]; exact hd _
  rw [stopB_roundsU_eq a K β r s G hdeg] at hT
  obtain ⟨E, hE⟩ : ∃ E, E = a * G.1 ^ 5 := ⟨_, rfl⟩
  obtain ⟨num, hnum⟩ : ∃ m, m = (thrF β r s G.1).1 := ⟨_, rfl⟩
  obtain ⟨den, hden'⟩ : ∃ m, m = (thrF β r s G.1).2 := ⟨_, rfl⟩
  rw [← hE, ← hnum, ← hden'] at hT
  rw [← hnum, ← hden'] at hψ
  rw [← hden'] at hden
  rw [← hE]
  -- the filter
  set Q := Net.powL G.1 (Net.baseMat true G.1 d (adjTable G)) E with hQ
  have hQlen : Q.length ≤ G.1 := by rw [hQ, Net.length_powL]
  have hc0 : 0 < (Net.denBase (Net.bParams true) d : ℝ)⁻¹ ^ E := by
    have : (0 : ℝ) < Net.denBase (Net.bParams true) d := by
      simp only [Net.denBase, Net.bParams, ite_true]
      positivity
    positivity
  have hb01 : ∀ i, 0 ≤ (1 - G.eig i) / 2 := fun i ↦ by
    have := abs_le.1 (G.abs_eig_le_one i)
    linarith only [this.2]
  -- the noise: at most `t` eigenvalues at most `-(1 - g)`, and `(1 - g/2)^E` elsewhere
  set R := Finset.univ.filter fun i ↦ G.eig i ≤ -(1 - g) with hR
  have hRt : R.card ≤ t := by
    refine stopB_card_le G ⟨d, hd⟩ hl1 ht ?_
    rcases hgcase with h | h
    · rw [h]
      exact Or.inl hhi
    · exact Or.inr h
  have hRn : R.card ≤ G.1 := (Finset.card_le_univ R).trans (by simp)
  have hφl : ∀ i ∉ R, |((1 - G.eig i) / 2) ^ E| ≤ (1 - g / 2) ^ E := by
    intro i hi
    have hi' : -(1 - g) < G.eig i := by simpa [hR] using hi
    rw [abs_of_nonneg (pow_nonneg (hb01 i) _)]
    exact pow_le_pow_left₀ (hb01 i) (by linarith only [hi']) E
  have hℓ : 0 ≤ (1 - g / 2) ^ E := pow_nonneg (by linarith only [hg1]) E
  -- the test
  have hX : (0 : ℤ) < ((den ^ (2 * E) : ℕ) : ℤ) := by positivity
  have htest := stopB_test (E := E) (num := num) hd0 hden hψ
  have hnoise := noise_le_thr (K := K) hn hcc0 hg0 hg1 hβ1 hβ0 ha
  rw [← hE] at hnoise
  have h2R : (1 : ℝ) ≤ 2 ^ (R.card + 1) := one_le_pow₀ (by norm_num)
  have hτ : ((2 ^ (R.card + 1) - 1) * (1 - g / 2) ^ E) ^ 2 * (((den ^ (2 * E) : ℕ) : ℤ) : ℝ) ≤
      ((Net.denBase (Net.bParams true) d : ℝ)⁻¹ ^ E) ^ 2 *
        ((((2 * d * num) ^ (2 * E) : ℕ) : ℤ) : ℝ) := by
    rw [htest]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg (by linarith only [h2R]) hℓ)
      ?_ 2) (by positivity)
    have h1 : (2 : ℝ) ^ (R.card + 1) - 1 ≤ 2 ^ (G.1 + 1) := by
      have : (2 : ℝ) ^ (R.card + 1) ≤ 2 ^ (G.1 + 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      linarith only [this]
    exact (mul_le_mul_of_nonneg_right h1 hℓ).trans hnoise
  have hP := stopB_hP G hd hdpos E
  -- the stopping round
  have hstop := (Net.stopZ_le_and_resid G.normAdj_isHermitian Q hQlen
    (Net.rowEntry_powL_symm true G d E) hc0 (fun i ↦ ((1 - G.eig i) / 2) ^ E) hP R hℓ hφl hX
    hτ).1
  rw [hT] at hstop
  refine ⟨hstop.trans hRt, fun B hB w hw1 hw ↦ ?_⟩
  -- the target
  have hcg : 0 ≤ cc * g := by positivity
  have hh0 : 0 < 1 - (1 - cc) * g / 2 := by linarith only [hcg, hg1]
  have hw' : ∀ i, Spectral.coeff G.normAdj_isHermitian i w ≠ 0 →
      (1 - (1 - cc) * g / 2) ^ E ≤ ((1 - G.eig i) / 2) ^ E := by
    intro i hi
    have hle : G.eig i ≤ -(1 - (1 - cc) * g) := by
      by_contra hcon
      exact hi (hw i hcon)
    exact pow_le_pow_left₀ hh0.le (by linarith only [hle]) E
  have hψ0 : 0 ≤ (1 - (1 - 1 / (β : ℝ)) * g / 2) ^ E := by
    rw [← hψ]
    positivity
  have hN : 0 < (Nat.sqrt T + 1) * K := Nat.mul_pos (Nat.succ_pos _) hK
  obtain ⟨-, cand, hcand, hdist⟩ := Net.exists_cand_near_stop G.normAdj_isHermitian Q hQlen
    (Net.rowEntry_powL_symm true G d E) hc0 (fun i ↦ ((1 - G.eig i) / 2) ^ E) hP R hℓ hφl hX
    hτ hψ0 (le_of_eq htest) (pow_pos hh0 E) w hw1 hw' hN (by rw [hT]; exact hB)
  rw [hT] at hcand hdist
  refine ⟨cand, ?_, hdist.trans ?_⟩
  · rw [Net.netGS, Net.gsData_graph true E T G hdeg]
    exact hcand
  · have hfilt := thr_le_target hn hK hcc0 hcc1 hg0 hg1 hβ2 ha
    rw [← hE] at hfilt
    have e : (4 : ℝ) / K = 2 / K + 2 / K := by ring
    rw [e]
    exact add_le_add (stopB_grid T hK) hfilt

/-! ### The guarantee -/

open Classical in
/-- **The number of rounds** is at most `t` on a regular graph with at most `t` eigenvalues at
most `-λ`, for parameters `(a, K, β, r, s)` with `a ≥ 40 (3 + K/2) / c''`, `c''/5 ≤ 1/β ≤ c''/4`
and `0 < r / s ≤ 1 - λ`. -/
theorem roundsU_le (G : Graph) (hreg : G.IsRegular) {lam : ℝ} (hl1 : lam < 1) {t : ℕ}
    (ht : (Finset.univ.filter fun i ↦ G.eig i ≤ -lam).card ≤ t) {cc : ℝ} (hcc0 : 0 < cc)
    (hcc1 : cc ≤ 1 / 32) {a K β r s : ℕ} (hK : 0 < K) (ha : 40 * (3 + K / 2 : ℝ) / cc ≤ a)
    (hβ1 : cc / 5 ≤ 1 / (β : ℝ)) (hβ2 : 1 / (β : ℝ) ≤ cc / 4) (hr : 0 < r) (hrs : r ≤ s)
    (hhi : (r : ℝ) / s ≤ 1 - lam) :
    roundsU (a, K, β, r, s) (G.1, adjTable G) ≤ t := by
  obtain ⟨d, hd⟩ := hreg
  rcases Nat.eq_zero_or_pos G.1 with hn0 | hn
  · have h := stopB_roundsU_le_numV (a, K, β, r, s) (G.1, adjTable G)
    rw [numV_graph] at h
    omega
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    rw [stopB_roundsU_deg_zero a K β r s G hd hn (stopB_a_pos hcc0 ha)
      (stopB_thr (stopB_one_le hcc0 hβ1) hn hr hrs).1]
    exact Nat.zero_le _
  · exact (stopB_net G hd hd0.ne' hn hl1 ht hcc0 (by linarith only [hcc1]) hK ha hβ1 hβ2 hr hrs
      hhi rfl).1

open Classical in
/-- **The guarantee of the algorithm** on a `d`-regular graph, `d ≥ 1`, with at most `t`
eigenvalues at most `-λ`, for the parameters of `BHSV25.Alg.roundsU_le` with
`(1 - c'') (1 - λ) ≤ r / s`: with a budget `B ≥ (3 + 12 K)^T` for the stopping round `T`, the
output has, for every independent set `I` and `η > 0`, at least
`|I| - (1 + η) 4 (n/2 - |I|) / ((1 - c'')² (1 - λ)) - (1 + 1/η) (4/K)² n` vertices. -/
theorem card_indepAlgU_ge (G : Graph) {d : ℕ} (hd : G.2.IsRegularOfDegree d) (hd0 : d ≠ 0)
    (hn : 0 < G.1) {lam : ℝ} (hl1 : lam < 1) {t : ℕ}
    (ht : (Finset.univ.filter fun i ↦ G.eig i ≤ -lam).card ≤ t) {cc : ℝ} (hcc0 : 0 < cc)
    (hcc1 : cc ≤ 1 / 32) {a K β r s : ℕ} (hK : 0 < K) (ha : 40 * (3 + K / 2 : ℝ) / cc ≤ a)
    (hβ1 : cc / 5 ≤ 1 / (β : ℝ)) (hβ2 : 1 / (β : ℝ) ≤ cc / 4) (hr : 0 < r) (hrs : r ≤ s)
    (hlo : (1 - cc) * (1 - lam) ≤ (r : ℝ) / s) (hhi : (r : ℝ) / s ≤ 1 - lam) (B B' : ℕ)
    (hB : (3 + 12 * K) ^ roundsU (a, K, β, r, s) (G.1, adjTable G) ≤ B)
    {I : Finset (Fin G.1)} (hI : G.2.IsIndepSet (I : Set (Fin G.1))) {η : ℝ} (hη : 0 < η) :
    (I.card : ℝ) - (1 + η) * 4 / ((1 - cc) ^ 2 * (1 - lam)) * (G.1 / 2 - I.card) -
        (1 + 1 / η) * (4 / K) ^ 2 * G.1 ≤
      (G.vertexSet (indepAlgU (a, K, β, r, s) ((B, B'), (G.1, adjTable G)))).card := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hl' : 0 < 1 - lam := by linarith only [hl1]
  have hcc1' : cc < 1 := by linarith only [hcc1]
  -- the algorithm with `T` rounds
  obtain ⟨T, hT⟩ : ∃ T, roundsU (a, K, β, r, s) (G.1, adjTable G) = T := ⟨_, rfl⟩
  rw [hT] at hB
  have hgoal : indepAlgU (a, K, β, r, s) ((B, B'), (G.1, adjTable G)) =
      indepAlgGS (a, T, (Nat.sqrt T + 1) * K, B) (G.1, adjTable G) := by
    simp only [indepAlgU, hT]
  rw [hgoal]
  have hstep := (stopB_net G hd hd0 hn hl1 ht hcc0 (by linarith only [hcc1]) hK ha hβ1 hβ2 hr
    hrs hhi hT).2
  obtain ⟨-, -, hg0, -, hgrs, -⟩ := stopB_gap hn hr hrs
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = ((gapF r s G.1).1 : ℝ) / (gapF r s G.1).2 := ⟨_, rfl⟩
  rw [← hg] at hg0 hgrs hstep
  have hg0' : 0 < g := lt_of_lt_of_le (by positivity) hg0
  -- the target
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 1 - (1 - cc) * g := ⟨_, rfl⟩
  rw [← hθ] at hstep
  have h1θ : 1 - θ = (1 - cc) * g := by rw [hθ]; ring
  have hθ1 : θ < 1 := by
    have : 0 < (1 - cc) * g := mul_pos (by linarith only [hcc1']) hg0'
    linarith only [this, h1θ]
  set u := signVec I with hu
  set w := Spectral.proj G.normAdj_isHermitian (· ≤ -θ) u with hw
  have hw1 : w ⬝ᵥ w ≤ 1 := (proj_dot_self_le _ _ _).trans (signVec_dot_self hn I).le
  have hw2 : G.InEigSpan (· ≤ -θ) w := Spectral.inEigSpan_proj _ _ _
  have hbud : Net.BallBudget ((Nat.sqrt T + 1) * K) T B :=
    fun i hi ↦ (Net.ballBudget_sqrt T K i hi).trans hB
  obtain ⟨c, hc, hcw⟩ := hstep B hbud w hw1 hw2
  have herr : (Net.vecOf G.1 c - w) ⬝ᵥ (Net.vecOf G.1 c - w) ≤ (4 / K) ^ 2 := by
    have h2 := Real.sq_sqrt (Net.dot_self_nonneg (Net.ratVec G.1 c - w))
    have h3 : Real.sqrt ((Net.ratVec G.1 c - w) ⬝ᵥ (Net.ratVec G.1 c - w)) ^ 2 ≤ (4 / K) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hcw 2
    rw [h2] at h3
    exact h3
  -- the candidate and the output
  have hcand := card_roundIndep_thrBits_ge G hd hd0 hn hI hθ1 hη c herr
  have hmem : c ∈ indepNet (a, T, (Nat.sqrt T + 1) * K, B) (G.1, adjTable G) := by
    rw [indepNet, numV_graph]
    exact hc
  have hle : ((G.vertexSet (roundIndep G.1 (adjTable G) (thrBits G.1 c))).card : ℝ) ≤
      (G.vertexSet (indepAlgGS (a, T, (Nat.sqrt T + 1) * K, B) (G.1, adjTable G))).card := by
    exact_mod_cast card_cand_le_indepAlg _ G hmem
  -- `1 - θ ≥ (1 - c'')² (1 - λ)`
  have hng0 : (0 : ℝ) ≤ G.1 / 2 - I.card := by
    have : (2 * I.card : ℝ) ≤ G.1 := by exact_mod_cast two_mul_card_le G hd hd0 hI
    linarith only [this]
  have hlow : (1 - cc) ^ 2 * (1 - lam) ≤ 1 - θ := by
    rw [h1θ, sq, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hlo.trans hgrs) (by linarith only [hcc1'])
  have hcoef : (1 + η) * 4 / (1 - θ) ≤ (1 + η) * 4 / ((1 - cc) ^ 2 * (1 - lam)) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos (pow_pos (by linarith only [hcc1']) 2) hl')
      hlow
  have := mul_le_mul_of_nonneg_right hcoef hng0
  linarith only [this, hcand, hle]

end BHSV25.Alg
