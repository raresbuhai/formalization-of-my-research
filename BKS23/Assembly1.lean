module

public import BKS23.Assembly
public import BKS23.Algorithm1
public import BKS23.SpectralCertificate
public import BKS23.SpectralNorm
public import BKS23.Rounding1
public import BKS23.Refine
public import BKS23.NonNeighbors
public import BKS23.Size1

/-!
# Assembly of Theorem 5.6 (1)

The proof of [BKS23, Theorem 5.6 (1)] from its parts.

* **The rounding, numerically** (`BKS23.Assembly1.near_numeric`): the solver's errors are small and
  the coverage is at least `k² / (4n)`.
* **Success on a good cut** (`BKS23.Assembly1.succeeds1_of_good`): if the centred cut matrix of a
  graph `R'` containing the cut of the random graph `R` has norm at most `√(18 n q (1 - q))`,
  every vertex outside the planted set `U` has at least `(1 - q) k / 2` non-neighbours in `U` in
  `R'`, the cut of `R` has no large bicliques, and the numerical conditions hold, the algorithm
  succeeds for every coin string.
-/

@[expose] public section

namespace BKS23.Assembly1

open SoS MvPolynomial Finset Filter Topology

/-! ### The rounding, numerically -/

/-- **The numerical hypotheses of the rounding to a nearby set**, for `T = 1`: if `n ≤ k²` and the
solver's error `τ = (η + γ) ∏ (1 + ‖fᵢ‖₂)` satisfies `τ (M + 1000 (n + 1)³) ≤ 1`, the errors are
small and the coverage is at least `k² / (4n)`. -/
theorem near_numeric {n k : ℕ} {η γ PN M ε cov eH : ℝ} (hη : 0 < η) (hγ : 0 < γ)
    (hPN : 0 ≤ PN) (hM : 0 ≤ M) (hk : 1 ≤ k) (hkn : k ≤ n) (hkk : n ≤ k ^ 2)
    (htiny : (η + γ) * PN * (M + 1000 * ((n : ℝ) + 1) ^ 3) ≤ 1)
    (hlam : γ / (η + γ) * (5 * n) ≤ 1 / 8) (hηγ : η + γ ≤ 1 / 8)
    (hε : ε = (η + γ) * (2 * 10 ^ (1 + 1)) * PN)
    (hcov : cov = (k - ε) ^ 2 / n - γ / (η + γ) * (4 * n + k) - (η + γ))
    (heH : eH = (η + γ) * PN * (2 * ((1 : ℕ) : ℝ) ^ 2 * (30 * k + 20) ^ 1)) :
    ε ≤ 1 ∧ ε ≤ k ∧ 0 < cov ∧ 0 < cov ^ 1 - eH ∧ (k : ℝ) ^ 2 / (4 * n) ≤ cov ^ 1 - eH ∧
      (η + γ) * M * PN + 2 * (k : ℝ) ^ 1 * (n + 1) * ε ≤ 1 := by
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = (η + γ) * PN := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn1 : (1 : ℝ) ≤ n := hk1.trans hkn'
  have hn0 : (0 : ℝ) < n := by linarith
  have hkk' : (n : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hkk
  have hτZ : τ * (M + 1000 * ((n : ℝ) + 1) ^ 3) ≤ 1 := by rw [hτ]; exact htiny
  have hn3 : (8 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by
    have : (2 : ℝ) ≤ n + 1 := by linarith
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) this 3
  have hn13 : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have hn23 : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 3 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hτM : τ * M ≤ 1 - τ * (1000 * ((n : ℝ) + 1) ^ 3) := by nlinarith
  have hτn : τ * (1000 * ((n : ℝ) + 1) ^ 3) ≤ 1 := by nlinarith [mul_nonneg hτ0 hM]
  have hετ : ε = 200 * τ := by rw [hε, hτ]; ring
  have hτ8 : τ * 8000 ≤ 1 := by nlinarith
  have hε8 : ε ≤ 1 / 8 := by rw [hετ]; linarith
  have hε0 : 0 ≤ ε := by rw [hετ]; positivity
  -- The coverage is at least `k² / (2n)`.
  have hlam0 : 0 ≤ γ / (η + γ) := by positivity
  have hcovc : (k : ℝ) ^ 2 / (2 * n) ≤ cov := by
    rw [hcov]
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
  -- `eH ≤ 1/10 ≤ k² / (4n)`.
  have heH1 : eH ≤ k ^ 2 / (4 * n) := by
    have h1 : eH = τ * (60 * k + 40) := by rw [heH, hτ]; push_cast; ring
    have h2 : τ * (60 * (k : ℝ) + 40) ≤ τ * (1000 * ((n : ℝ) + 1) ^ 3) / 10 := by
      have : 60 * (k : ℝ) + 40 ≤ 100 * ((n : ℝ) + 1) ^ 3 := by linarith
      have h' := mul_le_mul_of_nonneg_left this hτ0
      linarith
    have h3 : (1 : ℝ) / 4 ≤ (k : ℝ) ^ 2 / (4 * n) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    linarith
  have hcovk : (k : ℝ) ^ 2 / (4 * n) ≤ cov ^ 1 - eH := by
    rw [pow_one]
    have : (k : ℝ) ^ 2 / (2 * n) = 2 * ((k : ℝ) ^ 2 / (4 * n)) := by ring
    linarith
  have hpos : 0 < (k : ℝ) ^ 2 / (4 * n) := by positivity
  refine ⟨by linarith, by linarith, by linarith [hcovc, (by positivity : (0 : ℝ) <
    (k : ℝ) ^ 2 / (2 * n))], by linarith, hcovk, ?_⟩
  -- The rest of the numerator.
  have h1 : (η + γ) * M * PN = τ * M := by rw [hτ]; ring
  have h2 : 2 * (k : ℝ) ^ 1 * (n + 1) * ε ≤ τ * (1000 * ((n : ℝ) + 1) ^ 3) := by
    rw [hετ, pow_one]
    have hk' : (k : ℝ) * (n + 1) ≤ ((n : ℝ) + 1) ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have : 400 * (k : ℝ) * (n + 1) ≤ 1000 * ((n : ℝ) + 1) ^ 3 := by linarith
    have h' := mul_le_mul_of_nonneg_left this hτ0
    linarith
  linarith

/-! ### Success on a good cut -/

/-- The certificate's norm is at most `(20n + 3)^12`, when `1 ≤ Λ ≤ 18 n` and `1/(1 - q) ≤ n`. -/
theorem specNorm_le {n : ℕ} {Λ q : ℝ} (hΛ1 : 1 ≤ Λ) (hΛn : Λ ≤ 18 * n) (hq1 : q < 1)
    (hq' : 1 / (1 - q) ≤ n) :
    ((n : ℝ) + Λ + 1 / Λ + 1 / (1 - q) + 2) ^ 12 ≤ (20 * (n : ℝ) + 3) ^ 12 := by
  have h1 : 1 / Λ ≤ 1 := by rw [div_le_one (by linarith)]; exact hΛ1
  have hq10 : 0 < 1 - q := by linarith
  have h0 : 0 ≤ 1 / (1 - q) := by positivity
  refine pow_le_pow_left₀ (by positivity) ?_ 12
  linarith

/-- **The numbers of the rounding**, for the clique program of degree `6` with at most `n²`
non-edges and a certificate of norm `M ≤ (20n + 3)^12`. -/
theorem round_numbers {n k : ℕ} {L : List (ℕ × ℕ)} (hk : 1 ≤ k) (hkn : k ≤ n) (hkk : n ≤ k ^ 2)
    (hLlen : L.length ≤ n ^ 2) {M : ℝ} (hM0 : 0 ≤ M) (hMle : M ≤ (20 * (n : ℝ) + 3) ^ 12)
    (htiny : ((Algorithm.accη n 0 : ℝ) + Algorithm.accγ n 0) * 2 ^ (2 * (n + 2) ^ 3) *
      Size1.zOf n ≤ 1)
    (hlam : (Algorithm.accγ n 0 : ℝ) / (Algorithm.accη n 0 + Algorithm.accγ n 0) * (5 * n) ≤ 1 / 8)
    (hηγ : (Algorithm.accη n 0 : ℝ) + Algorithm.accγ n 0 ≤ 1 / 8) :
    let η : ℝ := Algorithm.accη n 0
    let γ : ℝ := Algorithm.accγ n 0
    let ε := Rounding.err n k (Algorithm.deg 0) L η γ 1
    let cov := Rounding.coverage n k η γ ε
    let eH := Rounding.errH n k (Algorithm.deg 0) L η γ 1
    ε ≤ 1 ∧ ε ≤ k ∧ 0 < cov ∧ 0 < cov ^ 1 - eH ∧ (k : ℝ) ^ 2 / (4 * n) ≤ cov ^ 1 - eH ∧
      (η + γ) * M * Rounding.constraintNorm n k (Algorithm.deg 0) L +
        2 * (k : ℝ) ^ 1 * (n + 1) * ε ≤ 1 := by
  intro η γ ε cov eH
  have hPN := Assembly.constraintNorm_le (ℓ := Algorithm.deg 0) hkn hLlen
  have hPN0 := Rounding.constraintNorm_nonneg n k (Algorithm.deg 0) L
  have hηγ0 : (0 : ℝ) ≤ η + γ := by
    have := Assembly.accη_pos n 0; have := Assembly.accγ_pos n 0; linarith
  have htiny' : (η + γ) * Rounding.constraintNorm n k (Algorithm.deg 0) L *
      (M + 1000 * ((n : ℝ) + 1) ^ 3) ≤ 1 := by
    refine le_trans ?_ htiny
    unfold Size1.zOf
    have hc0 : 0 ≤ M + 1000 * ((n : ℝ) + 1) ^ 3 :=
      add_nonneg hM0 (mul_nonneg (by norm_num) (pow_nonneg (by positivity) 3))
    have hb0 : 0 ≤ (η + γ) * (2 : ℝ) ^ (2 * (n + 2) ^ 3) :=
      mul_nonneg hηγ0 (pow_nonneg (by norm_num) _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hPN hηγ0) (add_le_add hMle le_rfl) hc0 hb0
  exact near_numeric (ε := ε) (cov := cov) (eH := eH) (Assembly.accη_pos n 0)
    (Assembly.accγ_pos n 0) hPN0 hM0 hk hkn hkk htiny' hlam hηγ rfl rfl rfl

/-- **Some `S_i` is near the planted set.** If the clique program of `G` is solved as the solver
does, and the cut of `G` is inside that of a graph `R'` whose centred cut matrix has norm at
most `√(18 n q (1 - q))`, then some `S_i = {j | Ẽ[wᵢ] ≤ 2 Ẽ[wᵢ wⱼ]}` differs from the planted
set `U` in at most `32 n (18 n q / (1 - q) + 1) / k²` vertices. -/
theorem exists_near {n k : ℕ} {G R' : SimpleGraph (Fin n)} {U : Finset (Fin n)}
    (hS : G.IsNClique k U) {E : PseudoExpectation (Fin n) (Algorithm.deg 0)}
    (hA : E.ApproxSatisfies (Clique.problem n k (Algorithm.deg 0)
      (Algorithm.nonEdges n (adjBits G))).system
        ((Algorithm.accη n 0 : ℝ) + (Algorithm.accγ n 0 : ℝ)) 0)
    (hopt : ∀ E' : PseudoExpectation (Fin n) (Algorithm.deg 0),
      E'.ApproxSatisfies (Clique.problem n k (Algorithm.deg 0)
        (Algorithm.nonEdges n (adjBits G))).system (Algorithm.accη n 0 : ℝ) 0 →
      (Clique.problem n k (Algorithm.deg 0) (Algorithm.nonEdges n (adjBits G))).objective E ≤
        (Clique.problem n k (Algorithm.deg 0) (Algorithm.nonEdges n (adjBits G))).objective E' +
          (Algorithm.accγ n 0 : ℝ))
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hcutG : ∀ u ∈ U, ∀ v ∈ Uᶜ, G.Adj u v → R'.Adj u v)
    (hnorm : Spectral.NormLE q U (18 * n * (q * (1 - q))) R')
    (hk : 1 ≤ k) (hkn : k ≤ n) (hkk : n ≤ k ^ 2)
    (hΛ1 : 1 ≤ 18 * n * (q * (1 - q))) (hq' : 1 / (1 - q) ≤ n)
    (htiny : ((Algorithm.accη n 0 : ℝ) + Algorithm.accγ n 0) * 2 ^ (2 * (n + 2) ^ 3) *
      Size1.zOf n ≤ 1)
    (hlam : (Algorithm.accγ n 0 : ℝ) / (Algorithm.accη n 0 + Algorithm.accγ n 0) * (5 * n) ≤ 1 / 8)
    (hηγ : (Algorithm.accη n 0 : ℝ) + Algorithm.accγ n 0 ≤ 1 / 8) :
    ∃ i : Fin n, (((univ.filter fun j ↦ E (X i) ≤ 2 * E (X i * X j)) \ U).card +
      (U \ univ.filter fun j ↦ E (X i) ≤ 2 * E (X i * X j)).card : ℝ) ≤
        32 * n * (18 * n * q / (1 - q) + 1) / (k : ℝ) ^ 2 := by
  set L := Algorithm.nonEdges n (adjBits G)
  have hLc := Algorithm.listsNonEdges G
  have hLs := Algorithm.onlyNonEdges G
  have hLlen : L.length ≤ n ^ 2 := Assembly.length_nonEdges_le n _
  set Λ := 18 * (n : ℝ) * (q * (1 - q)) with hΛ
  have hq10 : 0 < 1 - q := by linarith
  have hcert : DerivesN (Clique.realSystem n k (Algorithm.deg 0) L) 6
      (((n : ℝ) + Λ + 1 / Λ + 1 / (1 - q) + 2) ^ 12)
      (C (Λ / (1 - q) ^ 2) - (∑ u ∈ U, X u) ^ 1 * ∑ v ∈ Uᶜ, X v) :=
    (Spectral.certificate_spectral (k := k) (ℓ := Algorithm.deg 0) (Algorithm.listsNonEdges G)
      hcutG hq0.le hq1 (by linarith) hnorm).congr (by rw [pow_one])
  have hM0 : 0 ≤ ((n : ℝ) + Λ + 1 / Λ + 1 / (1 - q) + 2) ^ 12 := by
    have : 0 ≤ 1 / Λ := by positivity
    have : 0 ≤ 1 / (1 - q) := by positivity
    have : 0 ≤ Λ := by positivity
    positivity
  have hΛn : Λ ≤ 18 * n := by
    have hqq : q * (1 - q) ≤ 1 := by
      calc q * (1 - q) ≤ 1 * 1 := mul_le_mul hq1.le (by linarith) hq10.le zero_le_one
        _ = 1 := one_mul 1
    have := mul_le_mul_of_nonneg_left hqq (by positivity : (0 : ℝ) ≤ 18 * n)
    rw [hΛ]; linarith
  obtain ⟨h1, h2, h3, h4, hcovk, hrest⟩ := round_numbers (L := L) hk hkn hkk hLlen hM0
    (specNorm_le hΛ1 hΛn hq1 hq') htiny hlam hηγ
  obtain ⟨Q, hQ⟩ := Rounding.exists_round_near_eq (ℓ := Algorithm.deg 0) (T := 1) (D := 6) hS hLc
    hLs (Assembly.accη_pos n 0) (Assembly.accγ_pos n 0) (Assembly.accγ_le_accη n 0) hA hopt
    (by simp [Algorithm.deg]) (by simp [Algorithm.deg]) hcert h1 h2 h3 h4
  have hwQ : Rounding.wQ Q = X (Q 0) := by simp [Rounding.wQ]
  rw [hwQ] at hQ
  refine ⟨Q 0, hQ.trans ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hk0 (by exact_mod_cast hkn)
  have hω : Λ / (1 - q) ^ 2 = 18 * n * q / (1 - q) := by
    rw [hΛ]; field_simp
  rw [← hω]
  have hY : 0 < (k : ℝ) ^ 2 / (4 * n) := by positivity
  have hnum := add_le_add (le_refl (Λ / (1 - q) ^ 2)) hrest
  rw [← add_assoc] at hnum
  calc _ ≤ 8 * (Λ / (1 - q) ^ 2 + 1) / ((k : ℝ) ^ 2 / (4 * n)) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnum (by norm_num)) hY hcovk
    _ = 32 * n * (Λ / (1 - q) ^ 2 + 1) / (k : ℝ) ^ 2 := by field_simp; ring

open Classical in
/-- **The algorithm succeeds on a good cut.** Let `U` be the planted set and `R` the random graph,
and `R'` a graph containing the cut of `R`. If the centred cut matrix of `R'` has norm at most
`√Λ`, `Λ = 18 n q (1 - q)`, every vertex outside `U` has at least `(1 - q) k / 2` non-neighbours
in `U` in `R'`, the cut of `R` has no biclique with `Δ` vertices in `U`, and the numerical
conditions hold, then for every coin string the output on `G = Adv.graph U R` is a list of
`k`-cliques of `G`, containing `U`, of at most `(n/k)(1 + 2nΔ/k²)` entries. -/
theorem succeeds1_of_good {n k : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (Adv : Adversary n)
    {U : Finset (Fin n)} (hU : U.card = k) {R R' : SimpleGraph (Fin n)}
    (hRR' : ∀ u ∈ U, ∀ v ∈ Uᶜ, R.Adj u v → R'.Adj u v)
    (hnorm : Spectral.NormLE q U (18 * n * (q * (1 - q))) R')
    (hnon : Random.NonNbrGE U (1 - q) R')
    (hnb : Random.NoBiclique U (Algorithm.delta1 n k) R)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hkk : n ≤ k ^ 2)
    (hΛ1 : 1 ≤ 18 * n * (q * (1 - q))) (hq' : 1 / (1 - q) ≤ n)
    (hmain : 32 * n * (18 * n * q / (1 - q) + 1) / (k : ℝ) ^ 2 + 1 < (1 - q) * k / 2)
    (htiny : ((Algorithm.accη n 0 : ℝ) + Algorithm.accγ n 0) * 2 ^ (2 * (n + 2) ^ 3) *
      Size1.zOf n ≤ 1)
    (hlam : (Algorithm.accγ n 0 : ℝ) / (Algorithm.accη n 0 + Algorithm.accγ n 0) * (5 * n) ≤ 1 / 8)
    (hηγ : (Algorithm.accη n 0 : ℝ) + Algorithm.accγ n 0 ≤ 1 / 8)
    (hΔk : Algorithm.delta1 n k ≤ k) (h2 : 2 * n * Algorithm.delta1 n k ≤ k ^ 2)
    {bound : ℝ} (hbound : n / k * (1 + 2 * n * Algorithm.delta1 n k / (k : ℝ) ^ 2) ≤ bound)
    (r : List Bool) :
    Succeeds k (Adv.graph U R) U bound (Algorithm.alg1 (input (Adv.graph U R) k, r)) := by
  set G := Adv.graph U R
  have hS : G.IsNClique k U := by
    refine ⟨fun u hu v hv huv ↦ Adv.clique U R u hu v hv huv, hU⟩
  obtain ⟨E, hA, hopt, hcl, hmem, hlen⟩ := Algorithm.alg1_spec G hS r
  have hcutR : ∀ u ∈ U, ∀ v ∉ U, G.Adj u v → R.Adj u v := fun u hu v hv h ↦
    Adv.cut U R u v hu hv h
  have hcutG : ∀ u ∈ U, ∀ v ∈ Uᶜ, G.Adj u v → R'.Adj u v := fun u hu v hv h ↦
    hRR' u hu v hv (hcutR u hu v (mem_compl.1 hv) h)
  obtain ⟨i, hnear⟩ := exists_near hS hA hopt hq0 hq1 hcutG hnorm hk hkn hkk hΛ1 hq' htiny hlam hηγ
  set Si := univ.filter fun j ↦ E (X i) ≤ 2 * E (X i * X j) with hSi
  -- The refinement.
  set N₀ := ⌈(1 - q) * k / 2⌉₊
  have hnon' : ∀ v ∉ U, N₀ ≤ (U.filter fun u ↦ ¬ G.Adj u v).card := by
    intro v hv
    refine Nat.ceil_le.2 ?_
    have h := hnon v (mem_compl.2 hv)
    rw [hU] at h
    refine h.trans ?_
    have hsub : (U.filter fun u ↦ ¬ R'.Adj u v) ⊆ U.filter fun u ↦ ¬ G.Adj u v := by
      intro u hu
      rw [mem_filter] at hu ⊢
      exact ⟨hu.1, fun h' ↦ hu.2 (hcutG u hu.1 v (mem_compl.2 hv) h')⟩
    exact Nat.cast_le.2 (card_le_card hsub)
  have hsmall : (Si \ U).card + (U \ Si).card + 1 < N₀ := by
    have hN : (1 - q) * k / 2 ≤ (N₀ : ℝ) := Nat.le_ceil _
    have : ((Si \ U).card + (U \ Si).card + 1 : ℝ) < N₀ := by linarith only [hnear, hmain, hN]
    exact_mod_cast this
  obtain ⟨τ, hτ, hτU⟩ := Refine.exists_threshold hS hnon' hsmall
  refine ⟨?_, hcl, ?_⟩
  · exact hmem i τ U hτ hτU hS fun S' hS' hne ↦ Cleanup.card_inter_lt hU hnb hcutR hS' hne
  · exact (hlen (by omega) hΔk h2).trans hbound

/-! ### The numerical conditions from the size condition -/

/-- The main inequality of the rounding and the refinement:
`32 n (18 n q / (1 - q) + 1) / k² + 1 < (1 - q) k / 2`. -/
theorem main_ineq {n k : ℕ} {q : ℝ} (hk : 0 < (k : ℝ)) (hq1 : 0 < 1 - q)
    (hc : 4608 * (n : ℝ) ^ 2 * q ≤ (1 - q) ^ 2 * (k : ℝ) ^ 3)
    (h1024 : 1024 * n * Real.log n ^ 2 ≤ (k : ℝ) ^ 2) (hlog : 1 ≤ Real.log n)
    (h16 : 16 ≤ (1 - q) * k) :
    32 * n * (18 * n * q / (1 - q) + 1) / (k : ℝ) ^ 2 + 1 < (1 - q) * k / 2 := by
  have hk2 : 0 < (k : ℝ) ^ 2 := by positivity
  have e : 32 * (n : ℝ) * (18 * n * q / (1 - q) + 1) / (k : ℝ) ^ 2 =
      576 * (n : ℝ) ^ 2 * q / ((1 - q) * (k : ℝ) ^ 2) + 32 * n / (k : ℝ) ^ 2 := by
    field_simp; ring
  have h1 : 576 * (n : ℝ) ^ 2 * q / ((1 - q) * (k : ℝ) ^ 2) ≤ (1 - q) * k / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 - q) * (k : ℝ) / 8 * ((1 - q) * (k : ℝ) ^ 2) * 8 = (1 - q) ^ 2 * (k : ℝ) ^ 3 := by
      ring
    nlinarith
  have h2 : 32 * (n : ℝ) / (k : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one hk2]
    have hl2 : 1 ≤ Real.log n ^ 2 := one_le_pow₀ hlog
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  rw [e]
  linarith

open MeasureTheory ProbabilityTheory SimpleGraph in
/-- For `p ≤ q`, the probability under `G(n, p)` that the graph lies inside no graph with a
property `P` is at most the probability under `G(n, q)` that `P` fails: the coupling
`BKS23.Random.binomialRandom_le_of_antitone`. -/
theorem prob_not_exists_le {n : ℕ} {p q : unitInterval} (hpq : p ≤ q)
    (P : SimpleGraph (Fin n) → Prop) :
    (G(Fin n, p)).real {R | ¬ ∃ R', R ≤ R' ∧ P R'} ≤ (G(Fin n, q)).real {R | ¬ P R} := by
  set A : Set (SimpleGraph (Fin n)) := {R | ∃ R', R ≤ R' ∧ P R'}
  have hA : MeasurableSet A := MeasurableSet.of_discrete
  have hanti : ∀ R R', R ≤ R' → R' ∈ A → R ∈ A := fun R R' h ⟨R'', h', hg⟩ ↦ ⟨R'', h.trans h', hg⟩
  have hmono : (G(Fin n, q)).real A ≤ (G(Fin n, p)).real A := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
      (Random.binomialRandom_le_of_antitone hpq hA hanti)
  have hsub : {R | P R} ⊆ A := fun R h ↦ ⟨R, le_rfl, h⟩
  have h1 := MeasureTheory.measureReal_mono (μ := G(Fin n, q)) hsub
    (MeasureTheory.measure_ne_top _ _)
  have h2 : (G(Fin n, q)).real {R | ¬ P R} = 1 - (G(Fin n, q)).real {R | P R} :=
    MeasureTheory.probReal_compl_eq_one_sub (μ := G(Fin n, q)) (s := {R | P R})
      MeasurableSet.of_discrete
  have h3 : (G(Fin n, p)).real {R | ¬ ∃ R', R ≤ R' ∧ P R'} = 1 - (G(Fin n, p)).real A := by
    rw [← MeasureTheory.probReal_compl_eq_one_sub hA]
    rfl
  rw [h3]
  linarith

open MeasureTheory ProbabilityTheory unitInterval SimpleGraph in
/-- **The success probability for large `n`** is at least `0.99`, for every `p ∈ [0, 1)` and
every `k` with `32 max{n^(2/3) p^(1/3) / (1 - p)^(2/3), √n log n} ≤ k ≤ n`, every planted
`k`-set, every adversary, and every number of coins. -/
theorem le_successProb1 {n : ℕ} (hL : Size1.Large n) {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) {k : ℕ}
    (hsize : 32 * max ((n : ℝ) ^ (2 / 3 : ℝ) * p ^ (1 / 3 : ℝ) / (1 - p) ^ (2 / 3 : ℝ))
      (√(n : ℝ) * Real.log n) ≤ k) (hkn : k ≤ n) {S : Finset (Fin n)} (hU : S.card = k)
    (Adv : Adversary n) (T : ℕ → ℕ) :
    0.99 ≤ successProb n k p S Adv Algorithm.alg1 T ((1 + Size1.δ1 n) * n / k) := by
  classical
  have hn : 1100 ≤ n := hL.n_ge
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlog := hL.log_ge
  -- The size condition.
  have hs1 : 32 * ((n : ℝ) ^ (2 / 3 : ℝ) * p ^ (1 / 3 : ℝ) / (1 - p) ^ (2 / 3 : ℝ)) ≤ k :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)) hsize
  have hs2 : 32 * (√(n : ℝ) * Real.log n) ≤ k :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)) hsize
  have hc := Size1.cube_le hp hp1 hs1
  obtain ⟨hs3, h1024, hsk, hnk⟩ := Size1.sqrt_facts hn1 hlog hs2
  obtain ⟨hq0, hq1, hq', hqmain, hqk, hΛ1⟩ := Size1.q_facts (by omega) hp hp1 hkn hc hs3 hsk
  set q := max p (1 / √(n : ℝ)) with hqdef
  have hsn : (33 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hn0.le]
    have : (1100 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hk1 : 1 ≤ k := by omega
  have hkk : n ≤ k ^ 2 := by exact_mod_cast hnk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity) hq0
  have hq10 : 0 < 1 - q := by linarith
  have hsqn : √(n : ℝ) ≤ n := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith
  obtain ⟨hΔk, h2, hδ⟩ := Size1.delta1_facts hn1 hL.L2_ge hlog hk2 hkn h1024
  set pI : I := ⟨p, hp, hp1.le⟩
  set qI : I := ⟨q, hqpos.le, hq1.le⟩
  have hpq : pI ≤ qI := by
    change p ≤ q
    exact le_max_left _ _
  set Λ := 18 * (n : ℝ) * (q * (1 - q))
  set Δ := Algorithm.delta1 n k
  refine le_of_le_of_eq ?_ (Random.successProb_eq pI S Adv _ T _).symm
  set E : Set (SimpleGraph (Fin n)) := {R | (∃ R', R ≤ R' ∧
    (Spectral.NormLE q S Λ R' ∧ Random.NonNbrGE S (1 - q) R')) ∧ Random.NoBiclique S Δ R}
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  refine le_trans ?_ (Random.mul_measureReal_le_integral (μ := G(Fin n, pI)) (b := 1)
    Integrable.of_finite (fun R ↦ Assembly.coinProb_nonneg _ _) hE fun R hR ↦ ?_)
  swap
  · obtain ⟨⟨R', hRR', hnorm, hnon⟩, hnb⟩ := hR
    refine (Assembly.coinProb_eq_one fun r ↦ ?_).ge
    have h16 : 16 ≤ (1 - q) * k := by linarith
    have hmain := main_ineq (n := n) (k := k) (q := q) hk0 hq10 hqmain h1024 hlog h16
    refine succeeds1_of_good hqpos hq1 Adv hU (fun u _ v _ h ↦ hRR' h) hnorm hnon hnb hk1 hkn hkk
      hΛ1 (hq'.trans hsqn) hmain hL.tiny hL.lam (Assembly.acc_le n 0) hΔk h2 ?_ r
    have hδ' : 2 * n * (Δ : ℝ) / (k : ℝ) ^ 2 ≤ Size1.δ1 n := hδ
    calc (n : ℝ) / k * (1 + 2 * n * Δ / (k : ℝ) ^ 2) ≤ (n : ℝ) / k * (1 + Size1.δ1 n) :=
          mul_le_mul_of_nonneg_left (by linarith only [hδ']) (by positivity)
      _ = (1 + Size1.δ1 n) * n / k := by ring
  rw [one_mul]
  -- The bad events.
  have hA : (G(Fin n, pI)).real {R | ¬ ∃ R', R ≤ R' ∧
      (Spectral.NormLE q S Λ R' ∧ Random.NonNbrGE S (1 - q) R')} ≤ 1 / 200 := by
    refine (prob_not_exists_le hpq _).trans ?_
    have hsub : {R : SimpleGraph (Fin n) | ¬ (Spectral.NormLE q S Λ R ∧
        Random.NonNbrGE S (1 - q) R)} ⊆ {R | ¬ Spectral.NormLE q S Λ R} ∪
          {R | ¬ Random.NonNbrGE S (1 - q) R} := by
      intro R hR
      simp only [Set.mem_ofPred_eq, not_and_or] at hR
      exact hR
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans ?_)
    -- The norm of the cut.
    have hK : Biclique.charMax q * (2 * 2 ^ Size1.ell n + 1 : ℝ) ^ 4 ≤ n := by
      have h1 := Size1.charMax_le hq0 hq1 hq' hn1
      have h2' := hL.rmt
      have hs2 : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
      have : Biclique.charMax q * (2 * 2 ^ Size1.ell n + 1 : ℝ) ^ 4 ≤ √(n : ℝ) * √(n : ℝ) :=
        mul_le_mul h1 h2' (by positivity) (Real.sqrt_nonneg _)
      linarith
    have hN := Spectral.prob_not_normLE (q := qI) hqpos hq1 S (Size1.ell n) hK
    have hN' : (G(Fin n, qI)).real {R | ¬ Spectral.NormLE q S Λ R} ≤ 1 / 400 :=
      hN.trans hL.rmt_prob
    -- The non-neighbours.
    have hB := Random.prob_not_nonNbrGE S qI
    have hSc : (Sᶜ.card : ℝ) ≤ n := by
      have := card_le_univ Sᶜ
      simp only [Fintype.card_fin] at this
      exact_mod_cast this
    have hexp : Real.exp (-((1 - q) * S.card / 8)) ≤ Real.exp (-(√(n : ℝ) / 16)) := by
      rw [hU]
      exact Real.exp_le_exp.2 (by linarith)
    have hB' : (G(Fin n, qI)).real {R | ¬ Random.NonNbrGE S (1 - q) R} ≤ 1 / 400 := by
      refine hB.trans ?_
      calc (Sᶜ.card : ℝ) * Real.exp (-((1 - q) * S.card / 8))
          ≤ n * Real.exp (-(√(n : ℝ) / 16)) :=
            mul_le_mul hSc hexp (Real.exp_pos _).le hn0.le
        _ ≤ 1 / 400 := hL.nonnbr
    have : (1 : ℝ) / 400 + 1 / 400 = 1 / 200 := by norm_num
    linarith
  have hB : (G(Fin n, pI)).real {R | ¬ Random.NoBiclique S Δ R} ≤ 1 / 200 := by
    refine (Random.prob_not_noBiclique S pI Δ).trans ?_
    set x := (S.card : ℝ) * Sᶜ.card * (p : ℝ) ^ Δ with hx
    have hx0 : 0 ≤ x := by positivity
    have h1 : p ≤ Real.exp (-(1 - p)) := by
      have := Real.add_one_le_exp (-(1 - p)); linarith
    have h2' : p ^ Δ ≤ Real.exp (-((1 - p) * Δ)) := by
      calc p ^ Δ ≤ Real.exp (-(1 - p)) ^ Δ := pow_le_pow_left₀ hp h1 Δ
        _ = Real.exp (-((1 - p) * Δ)) := by rw [← Real.exp_nat_mul]; ring_nf
    have hnb := Size1.nb_facts (by omega) hp1 hlog hL.L2_le hL.nb hc h1024 hsk
    have h3 : Real.exp (-((1 - p) * Δ)) ≤ 1 / (400 * (n : ℝ) ^ 2) := by
      rw [show 1 / (400 * (n : ℝ) ^ 2) = Real.exp (-Real.log (400 * (n : ℝ) ^ 2)) by
        rw [Real.exp_neg, Real.exp_log (by positivity), one_div]]
      exact Real.exp_le_exp.2 (by linarith)
    have hcard : (S.card : ℝ) * Sᶜ.card ≤ (n : ℝ) ^ 2 := by
      have a : (S.card : ℝ) ≤ n := by rw [hU]; exact_mod_cast hkn
      have b : (Sᶜ.card : ℝ) ≤ n := by exact_mod_cast (card_le_univ _).trans (by simp)
      rw [sq]; exact mul_le_mul a b (by positivity) (by positivity)
    have hx1 : x ≤ 1 / 400 := by
      calc x ≤ (n : ℝ) ^ 2 * (1 / (400 * (n : ℝ) ^ 2)) :=
            mul_le_mul hcard (h2'.trans h3) (by positivity) (by positivity)
        _ = 1 / 400 := by field_simp
    have := Assembly.sum_geom_le hx0 (by linarith) S.card
    linarith
  have hsub : Eᶜ ⊆ {R | ¬ ∃ R', R ≤ R' ∧
      (Spectral.NormLE q S Λ R' ∧ Random.NonNbrGE S (1 - q) R')} ∪
      {R | ¬ Random.NoBiclique S Δ R} := by
    intro R hR
    simp only [E, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or] at hR
    exact hR
  have hc' : (G(Fin n, pI)).real Eᶜ ≤ 1 / 100 :=
    (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_union_le _ _).trans
      (by linarith))
  have := measureReal_add_measureReal_compl (μ := G(Fin n, pI)) hE
  rw [probReal_univ] at this
  norm_num
  linarith

end BKS23.Assembly1
