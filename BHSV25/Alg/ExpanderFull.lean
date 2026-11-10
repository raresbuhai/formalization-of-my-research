module

public import BHSV25.Alg.ExpanderGrid
public import BHSV25.Alg.GridPolyTime
public import BHSV25.Alg.IndepSetGS

/-!
# Theorem 7.1 and Corollary 7.2

[BHSV25, Theorem 7.1] (`BHSV25.Alg.expanderColoring_algorithm`): for every model `M` with
stationary distribution `π`, there are `B` and `c₀ > 0` such that for `δ ∈ [0, c₀)` and
`λ ∈ (0, c₀)` an algorithm running in time `K · m^C`, with `C` independent of `M`, `δ` and `λ`,
outputs a `(k', α + B (√δ + λ + δ/λ))`-coloring of every regular graph with at most one
eigenvalue above `λ` and an `(M, δ)`-coloring, where `k'` is the number of distinct rows of `M`.
Corollary 7.2 (`BHSV25.Alg.expanderColoring_distinctRows`) is the case of distinct rows.

**The algorithm** (`BHSV25.Alg.expAlg`) reads its parameters `((m, K₀, S, K, B), (a, T, N, B'))`
in unary with the graph: the greedy net of the eigenvectors with eigenvalues large in absolute
value (`BHSV25.Net.netGS` with the filter `Ã^(2 a n)`, `T` rounds, the ball of radius `N` cut at
`B'`), then the grid clustering of `BHSV25.Alg.gridAlg` with `m` clusters, the uncolored vertices
marked `K₀`, the grid of scale `S` and range `K`, and the budget `B`. One machine serves all
parameters (`BHSV25.Alg.expAlg_polytime`), so the degree `C` of its running time does not depend
on them.

**The parameters**, for `M`, `π` and the threshold `θ` of `BHSV25.Alg.exists_threshold`:
`m = K₀` the number of distinct rows, `T = ⌊1 + 4 / (θ/2)⁴⌋` (at most that many eigenvalues at
least `θ/2` in absolute value, `BHSV25.Alg.card_abs_eig_ge_le`), the precision `4 / K'` of the net
with `K'` large enough that its cost `512 m² (4/K')² / α²` is at most `λ`, `a = T + 2 + K'` so
that the filter's error `√n 2^(T+1) 4^(-a n)` is at most `2 / K'`, and the grid of
`BHSV25.Alg.exists_good_grid`.
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Finset Matrix Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-! ### The algorithm -/

/-- The net of Theorem 7.1 for the parameters `(a, T, N, B)`: the greedy net of the eigenvectors
with eigenvalues large in absolute value, with the filter `Ã^(2 a n)`. -/
def expNet (p : ℕ × ℕ × ℕ × ℕ) (x : ℕ × List Bool) : List (List ℚ) :=
  Net.netGS false (2 * (p.1 * numV x)) p.2.1 p.2.2.1 p.2.2.2 x

/-- **The algorithm** of [BHSV25, Theorem 7.1]: the grid clustering of the net. -/
def expAlg (p : (ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) (x : ℕ × List Bool) : List ℕ :=
  gridAlg p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 (expNet p.2 x) x

theorem expNet_polytime : ComputableInPolyTime
    (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ expNet z.1 z.2) encIndepIn
    (encList (encList encRat)) := by
  have hpar : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ z.1) encIndepIn
      Net.encGSPar := fst _ _
  have hx : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ z.2) encIndepIn
      (encPair encNat encBits) := snd _ _
  have ha := (fst _ _).comp hpar
  have hrest := (snd _ _).comp hpar
  have hn := numV_polytime.comp hx
  have hE := unary_mul' (const 2) (unary_mul' ha hn)
  have hp := hE.prod hrest
  have key := (Net.netGS_polytime false).comp (hp.prod hx)
  exact key

/-- The parameters of the algorithm, in unary. -/
abbrev encExpPar : (ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) ↪ List Bool :=
  encPair encGridPar Net.encGSPar

/-- **The algorithm runs in polynomial time**, reading its parameters in unary with the graph. -/
theorem expAlg_polytime : ComputableInPolyTime
    (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ expAlg z.1 z.2)
    (encPair encExpPar (encPair encNat encBits)) encColoring := by
  have hp1 : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ z.1.1)
      (encPair encExpPar (encPair encNat encBits)) encGridPar := (fst _ _).comp (fst _ _)
  have hp2 : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ z.1.2)
      (encPair encExpPar (encPair encNat encBits)) Net.encGSPar := (snd _ _).comp (fst _ _)
  have hx : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ z.2)
      (encPair encExpPar (encPair encNat encBits)) (encPair encNat encBits) := snd _ _
  have hU := expNet_polytime.comp (hp2.prod hx)
  have key := gridAlg_polytime.comp ((hp1.prod hU).prod hx)
  exact key

/-- The algorithm, with the colors in unary. -/
theorem expAlg_unary : ComputableInPolyTime
    (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ expAlg z.1 z.2)
    (encPair encExpPar (encPair encNat encBits)) (encList encUnary) := by
  have hp1 : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ z.1.1)
      (encPair encExpPar (encPair encNat encBits)) encGridPar := (fst _ _).comp (fst _ _)
  have hp2 : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ z.1.2)
      (encPair encExpPar (encPair encNat encBits)) Net.encGSPar := (snd _ _).comp (fst _ _)
  have hx : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ z.2)
      (encPair encExpPar (encPair encNat encBits)) (encPair encNat encBits) := snd _ _
  have hU := expNet_polytime.comp (hp2.prod hx)
  have key := gridAlg_unary.comp ((hp1.prod hU).prod hx)
  exact key

/-! ### The net -/

/-- **The filter's error**: for `n ≥ 1` and `a ≥ T + 2 + K`,
`√n 2^(T+1) ((θ/2) / θ)^(2 a n) ≤ 2 / K`. -/
theorem abs_filter_error_le {n T K a : ℕ} (hn : 0 < n) (hK : 0 < K) (ha : T + 2 + K ≤ a)
    {θ : ℝ} (hθ : 0 < θ) :
    Real.sqrt n * 2 ^ (T + 1) * (θ / 2 / θ) ^ (2 * (a * n)) ≤ 2 / K := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hr : θ / 2 / θ = 1 / 2 := by field_simp
  rw [hr]
  have hpow : ((1 : ℝ) / 2) ^ (2 * (a * n)) ≤ Real.exp (-(a * n : ℝ)) := by
    rw [pow_mul]
    have h4 : ((1 : ℝ) / 2) ^ 2 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, inv_eq_one_div, div_pow, one_pow, one_div_le_one_div (by norm_num)
        (Real.exp_pos 1)]
      linarith [Real.exp_one_lt_three]
    calc (((1 : ℝ) / 2) ^ 2) ^ (a * n) ≤ Real.exp (-1) ^ (a * n) :=
          pow_le_pow_left₀ (by positivity) h4 _
      _ = Real.exp (-(a * n : ℝ)) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hX : (n : ℝ) + (T + 1) + K / 2 ≤ a * n := by
    have h1 : ((T : ℝ) + 2 + K) * n ≤ a * n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast ha) (by positivity)
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    nlinarith
  have hsq : Real.sqrt n ≤ Real.exp n := by
    have h1 : Real.sqrt n ≤ n + 1 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    linarith [Real.add_one_le_exp (n : ℝ)]
  have h2 : (2 : ℝ) ^ (T + 1) ≤ Real.exp (T + 1) := by
    have h := Real.add_one_le_exp 1
    calc (2 : ℝ) ^ (T + 1) ≤ Real.exp 1 ^ (T + 1) :=
          pow_le_pow_left₀ (by norm_num) (by linarith) _
      _ = Real.exp (T + 1) := by rw [← Real.exp_nat_mul, mul_one]; push_cast; ring_nf
  calc Real.sqrt n * 2 ^ (T + 1) * ((1 : ℝ) / 2) ^ (2 * (a * n))
      ≤ Real.exp n * Real.exp (T + 1) * Real.exp (-(a * n : ℝ)) := by gcongr
    _ = Real.exp (n + (T + 1) - a * n) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(K / 2)) := Real.exp_le_exp.2 (by linarith)
    _ ≤ 2 / K := exp_neg_half_le hK'

/-- **The net covers the eigenvectors with eigenvalues at least `θ` in absolute value**, at
precision `4 / K`, on regular graphs with at most one eigenvalue above `λ < (θ/2)² / 2`. -/
theorem expNet_cover (G : Graph) (hreg : G.IsRegular) {lam θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 2)
    (hl : lam < (θ / 2) ^ 2 / 2) (hexp : G.numEigGT lam ≤ 1) {K a : ℕ} (hK : 0 < K)
    (ha : ⌊1 + 4 / (θ / 2) ^ 4⌋₊ + 2 + K ≤ a) (w : Fin G.1 → ℝ) (hw1 : w ⬝ᵥ w ≤ 1)
    (hw : G.InEigSpan (fun μ ↦ θ ≤ |μ|) w) :
    ∃ u ∈ expNet (a, ⌊1 + 4 / (θ / 2) ^ 4⌋₊, (Nat.sqrt ⌊1 + 4 / (θ / 2) ^ 4⌋₊ + 1) * K,
        (3 + 12 * K) ^ ⌊1 + 4 / (θ / 2) ^ 4⌋₊) (G.1, adjTable G),
      (Net.ratVec G.1 u - w) ⬝ᵥ (Net.ratVec G.1 u - w) ≤ (4 / K) ^ 2 := by
  set T := ⌊1 + 4 / (θ / 2) ^ 4⌋₊ with hT
  set N := (Nat.sqrt T + 1) * K with hN
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hNpos : 0 < N := Nat.mul_pos (Nat.succ_pos _) hK
  rw [expNet, numV_graph]
  simp only
  rcases Nat.eq_zero_or_pos G.1 with hn0 | hn
  · -- no vertices
    obtain ⟨c, hc, -⟩ := Net.exists_zero_mem_netGS false (2 * (a * G.1)) T N ((3 + 12 * K) ^ T) G
      (Net.ballBudget_sqrt T K)
    refine ⟨c, hc, ?_⟩
    have : (Net.ratVec G.1 c - w) ⬝ᵥ (Net.ratVec G.1 c - w) = 0 := by
      simp only [dotProduct]
      exact Finset.sum_eq_zero fun i _ ↦ absurd i.2 (by omega)
    rw [this]
    positivity
  have hcard : (univ.filter fun i ↦ θ / 2 ≤ |G.eig i|).card ≤ T :=
    Nat.le_floor (card_abs_eig_ge_le G (by positivity) (by linarith) hl hexp)
  obtain ⟨c, hc, hcw⟩ := Net.netGS_abs_correct G hreg (by positivity : 0 < θ / 2)
    (by linarith : θ / 2 < θ) hcard (a * G.1) hNpos (Net.ballBudget_sqrt T K) w hw1 hw
  refine ⟨c, hc, ?_⟩
  have hgrid : 2 * Real.sqrt T / N ≤ 2 / K := by
    have hs : Real.sqrt T ≤ (Nat.sqrt T + 1 : ℕ) := by
      push_cast
      exact (Real.real_sqrt_lt_nat_sqrt_succ).le
    rw [hN, Nat.cast_mul, div_le_div_iff₀ (by positivity) hK']
    have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * K)
    nlinarith
  have hfilt := abs_filter_error_le (T := T) hn hK ha hθ0
  have h1 : Real.sqrt ((Net.ratVec G.1 c - w) ⬝ᵥ (Net.ratVec G.1 c - w)) ≤ 4 / K := by
    refine hcw.trans ?_
    have : (4 : ℝ) / K = 2 / K + 2 / K := by ring
    rw [this]
    exact add_le_add hgrid hfilt
  have h2 := Real.sq_sqrt (Net.dot_self_nonneg (Net.ratVec G.1 c - w))
  have h3 : Real.sqrt ((Net.ratVec G.1 c - w) ⬝ᵥ (Net.ratVec G.1 c - w)) ^ 2 ≤ (4 / K) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [h2] at h3
  exact h3

/-- The net has at most `B + 1` vectors. -/
theorem length_expNet_le (p : ℕ × ℕ × ℕ × ℕ) (x : ℕ × List Bool) :
    (expNet p x).length ≤ p.2.2.2 + 1 := by
  rw [expNet, Net.netGS, Net.candsOf, List.length_map]
  exact (Net.ballTuples_iter_small _ _ _).2

/-! ### The arithmetic -/

/-- The uncovered fraction of the analysis is at most `B (√δ + λ + δ/λ)`. -/
theorem uncovered_le {m k : ℕ} {C δ lam K₁ F : ℝ} (hC : 0 ≤ C) (hK₁ : 0 ≤ K₁) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hl0 : 0 < lam) (hF : F ≤ lam) :
    m * ((2 * k + 2) * (C * δ)) + 2 * δ + 2 * (K₁ * ((2 + k) * δ / lam + lam) + F) ≤
      (m * (2 * k + 2) * C + 2 + 2 * K₁ * (2 + k) + 2 * K₁ + 2) *
        (Real.sqrt δ + lam + δ / lam) := by
  have hsq : δ ≤ Real.sqrt δ := by
    have h1 : Real.sqrt δ ≤ 1 := Real.sqrt_le_one.2 hδ1
    have h2 := Real.mul_self_sqrt hδ0
    nlinarith [Real.sqrt_nonneg δ]
  have hs0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hq0 : 0 ≤ δ / lam := div_nonneg hδ0 hl0.le
  have hA : (0 : ℝ) ≤ m * (2 * k + 2) * C := by positivity
  have e : (2 + (k : ℝ)) * δ / lam = (2 + k) * (δ / lam) := by ring
  rw [e]
  have h1 : (m : ℝ) * ((2 * k + 2) * (C * δ)) ≤ m * (2 * k + 2) * C * Real.sqrt δ := by
    have := mul_le_mul_of_nonneg_left hsq hA
    linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith [mul_nonneg hA hs0, mul_nonneg hA hq0, mul_nonneg hA hl0.le,
    mul_nonneg hK₁ hs0, mul_nonneg hK₁ hq0, mul_nonneg hK₁ hl0.le,
    mul_nonneg (mul_nonneg hK₁ hk0) hs0, mul_nonneg (mul_nonneg hK₁ hk0) hl0.le,
    mul_nonneg (mul_nonneg hK₁ hk0) hq0]

/-- The cost of the net, `512 m² (4/K)² / α² ≤ λ` for `K ≥ 32768 m² / (α_N² λ) + 1`. -/
theorem net_cost_le {m : ℕ} {αN lam : ℝ} (hαN : 0 < αN) (hl0 : 0 < lam) {K : ℕ}
    (hK : 32768 * (m : ℝ) ^ 2 / (αN ^ 2 * lam) + 1 ≤ K) :
    512 * (m : ℝ) ^ 2 * (4 / K) ^ 2 / (αN / 2) ^ 2 ≤ lam := by
  have hK1 : (1 : ℝ) ≤ K := by
    have : 0 ≤ 32768 * (m : ℝ) ^ 2 / (αN ^ 2 * lam) := by positivity
    linarith
  have hK2 : 32768 * (m : ℝ) ^ 2 / (αN ^ 2 * lam) ≤ (K : ℝ) ^ 2 := by nlinarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < αN ^ 2 * lam)] at hK2
  have e : 512 * (m : ℝ) ^ 2 * (4 / K) ^ 2 / (αN / 2) ^ 2 =
      32768 * (m : ℝ) ^ 2 / (αN ^ 2 * (K : ℝ) ^ 2) := by
    field_simp
    ring
  rw [e, div_le_iff₀ (by positivity)]
  nlinarith

/-! ### The guarantee -/

variable {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} {π : Fin k → ℝ}

/-- **The guarantee on one graph**, for the parameters of the algorithm. -/
theorem isColoring_expAlg (hM : IsModel M) (hπ : IsStationary M π) (hk : 0 < k) {C : ℝ}
    (hC : 0 < C)
    (hstab : ∀ (p : Fin k → ℝ) (ε : ℝ), ∑ a, p a = 1 →
      (∀ b, |∑ a, p a * M a b - p b| ≤ ε) → ∀ a, |p a - π a| ≤ C * ε)
    {αN : ℝ} (hαN : 0 < αN)
    (hsepN : ∀ i j : Reps M π, i ≠ j → ∃ l : Reps M π,
      αN ≤ |∑ b ∈ rowGroup M l.1, M i.1 b - ∑ b ∈ rowGroup M l.1, M j.1 b|)
    {πmin : ℝ} (hπmin : 0 < πmin) (hπle : ∀ a, πmin ≤ π a)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hθα : (2 * θ) ^ 2 * (2 / (πmin / 2)) ≤ (αN / 2) ^ 2 / 2)
    {δ lam : ℝ} (hδ0 : 0 ≤ δ) (hδk : k * δ < 1) (hδC : C * δ ≤ πmin / 2)
    (hδN : 2 * k * δ ≤ αN / 2) (hl0 : 0 < lam) (hl1 : lam < 1) (hlθ : lam < (θ / 2) ^ 2 / 2)
    {K a Sg Kg Bg : ℕ} (hK : 0 < K) (ha : ⌊1 + 4 / (θ / 2) ^ 4⌋₊ + 2 + K ≤ a)
    (hSg : 128 * (Fintype.card (Reps M π) : ℝ) ^ 2 ≤ (αN / 2) ^ 2 * (Sg : ℝ) ^ 2) (hK1 : 1 ≤ Kg)
    (hKg : (Sg : ℝ) ^ 2 ≤ πmin / 2 * ((Kg : ℝ) - 1) ^ 2)
    (hBg1 : ((3 + 12 * K) ^ ⌊1 + 4 / (θ / 2) ^ 4⌋₊ + 1) ^ Fintype.card (Reps M π) ≤ Bg)
    (hBg2 : (2 * Kg + 1) ^ (Fintype.card (Reps M π) * Fintype.card (Reps M π)) ≤ Bg)
    (G : Graph) (hreg : G.IsRegular) (hexp : G.numEigGT lam ≤ 1) (hcol : G.MColorable M δ) :
    G.IsColoring (Fintype.card (Reps M π))
      (alpha M π + (Fintype.card (Reps M π) * ((2 * k + 2) * (C * δ)) + 2 * δ +
        2 * (512 * (Fintype.card (Reps M π) : ℝ) ^ 4 * ((2 + k) * δ / lam + lam) /
          (πmin / 2 * (2 * θ - θ) ^ 2 * (αN / 2) ^ 2) +
          512 * (Fintype.card (Reps M π) : ℝ) ^ 2 * (4 / K) ^ 2 / (αN / 2) ^ 2)))
      (expAlg ((Fintype.card (Reps M π), Fintype.card (Reps M π), Sg, Kg, Bg),
        (a, ⌊1 + 4 / (θ / 2) ^ 4⌋₊, (Nat.sqrt ⌊1 + 4 / (θ / 2) ^ 4⌋₊ + 1) * K,
          (3 + 12 * K) ^ ⌊1 + 4 / (θ / 2) ^ 4⌋₊)) (G.1, adjTable G)) := by
  set m := Fintype.card (Reps M π) with hmdef
  have hm : 0 < m := Fintype.card_pos_iff.2 ⟨toRep M π ⟨0, hk⟩⟩
  set U := expNet (a, ⌊1 + 4 / (θ / 2) ^ 4⌋₊, (Nat.sqrt ⌊1 + 4 / (θ / 2) ^ 4⌋₊ + 1) * K,
    (3 + 12 * K) ^ ⌊1 + 4 / (θ / 2) ^ 4⌋₊) (G.1, adjTable G) with hU
  have hB1 : U.length ^ m ≤ Bg :=
    (Nat.pow_le_pow_left (length_expNet_le _ _) m).trans hBg1
  have hnet : ∀ w : Fin G.1 → ℝ, w ⬝ᵥ w ≤ 1 → G.InEigSpan (fun μ ↦ θ ≤ |μ|) w →
      ∃ u ∈ U, (Net.ratVec G.1 u - w) ⬝ᵥ (Net.ratVec G.1 u - w) ≤ (4 / K) ^ 2 :=
    fun w hw1 hw ↦ expNet_cover G hreg hθ0 (by linarith) hlθ hexp hK ha w hw1 hw
  refine ⟨(gridAlg_spec G hm le_rfl Sg Kg Bg U hB1 hBg2).1, ?_⟩
  exact expander_numColored_grid hM hπ hk hC hstab hαN hsepN hπmin hπle hθ0 hθα hδ0 hδk hδC
    hδN hl0 hl1 U hSg hK1 hKg hB1 hBg2 G hreg hexp hcol hnet

/-- **The threshold `θ`**: a rational in `(0, 1/2)` with `(2 θ)² (2 / c) ≤ α² / 2`. -/
theorem exists_threshold {αN πmin : ℝ} (hαN : 0 < αN) (hπmin : 0 < πmin) :
    ∃ θ : ℚ, (0 : ℝ) < θ ∧ (θ : ℝ) < 1 / 2 ∧
      (2 * (θ : ℝ)) ^ 2 * (2 / (πmin / 2)) ≤ (αN / 2) ^ 2 / 2 := by
  have hsqc : 0 < Real.sqrt (πmin / 2) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨θ, hθ0, hθ1⟩ : ∃ θ : ℚ, (0 : ℝ) < θ ∧
      (θ : ℝ) < min (1 / 2) (αN * Real.sqrt (πmin / 2) / 8) :=
    exists_rat_btwn (lt_min (by norm_num) (by positivity))
  refine ⟨θ, hθ0, lt_of_lt_of_le hθ1 (min_le_left _ _), ?_⟩
  have h1 : (θ : ℝ) ≤ αN * Real.sqrt (πmin / 2) / 8 :=
    (lt_of_lt_of_le hθ1 (min_le_right _ _)).le
  have h2 : (θ : ℝ) ^ 2 ≤ (αN * Real.sqrt (πmin / 2) / 8) ^ 2 := pow_le_pow_left₀ hθ0.le h1 2
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)] at h2
  have e1 : (2 * (θ : ℝ)) ^ 2 * (2 / (πmin / 2)) = 16 * (θ : ℝ) ^ 2 / πmin := by
    field_simp
    ring
  rw [e1, div_le_iff₀ hπmin]
  have e2 : (αN / 2) ^ 2 / 2 * πmin = 16 * (αN ^ 2 * (πmin / 2) / 8 ^ 2) := by ring
  rw [e2]
  linarith

/-- **The grid of centers**: a scale `S` and a range `K` with `128 m² ≤ (α/2)² S²` and
`S² ≤ c (K - 1)²`. -/
theorem exists_grid_params (m : ℕ) {αN c : ℝ} (hαN : 0 < αN) (hc : 0 < c) :
    ∃ Sg Kg : ℕ, 128 * (m : ℝ) ^ 2 ≤ (αN / 2) ^ 2 * (Sg : ℝ) ^ 2 ∧ 1 ≤ Kg ∧
      (Sg : ℝ) ^ 2 ≤ c * ((Kg : ℝ) - 1) ^ 2 := by
  refine ⟨⌈32 * m / αN⌉₊, ⌈(⌈32 * m / αN⌉₊ : ℝ) / Real.sqrt c⌉₊ + 1, ?_, by omega, ?_⟩
  · have h1 : 32 * (m : ℝ) / αN ≤ ⌈32 * m / αN⌉₊ := Nat.le_ceil _
    have h2 : 16 * (m : ℝ) ≤ αN / 2 * ⌈32 * m / αN⌉₊ := by
      rw [div_le_iff₀ hαN] at h1
      linarith
    have h3 : (16 * (m : ℝ)) ^ 2 ≤ (αN / 2 * ⌈32 * m / αN⌉₊) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    nlinarith
  · set Sg : ℝ := (⌈32 * m / αN⌉₊ : ℝ)
    have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
    have h1 : Sg / Real.sqrt c ≤ ⌈Sg / Real.sqrt c⌉₊ := Nat.le_ceil _
    push_cast
    rw [add_sub_cancel_right]
    have h2 : Sg ≤ Real.sqrt c * ⌈Sg / Real.sqrt c⌉₊ := by
      rw [div_le_iff₀ hsc] at h1
      linarith
    have h3 : Sg ^ 2 ≤ (Real.sqrt c * ⌈Sg / Real.sqrt c⌉₊) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    rw [mul_pow, Real.sq_sqrt hc.le] at h3
    exact h3

/-- **The parameters for a model**: `B` and `c₀` depending only on `M` and `π`, and for all
`δ ∈ [0, c₀)` and `λ ∈ (0, c₀)` parameters of the algorithm that color every regular graph with
at most one eigenvalue above `λ` and an `(M, δ)`-coloring. -/
theorem exists_expAlg_params (hM : IsModel M) (hπ : IsStationary M π) :
    ∃ B c₀ : ℝ, 0 < c₀ ∧ ∀ δ lam : ℝ, 0 ≤ δ → δ < c₀ → 0 < lam → lam < c₀ →
      ∃ p, ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.MColorable M δ →
        G.IsColoring (Nat.card (Set.range M)) (alpha M π + B * (Real.sqrt δ + lam + δ / lam))
          (expAlg p (G.1, adjTable G)) := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      have := hπ.2.1
      simp at this
    · exact h
  obtain ⟨C, hC, hstab⟩ := exists_stationary_stable M hM hπ
  obtain ⟨αN, hαN, hsepN⟩ := exists_sep_contracted (M := M) hπ
  have hne : (univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, mem_univ _⟩
  obtain ⟨πmin, hπmin_def⟩ : ∃ x : ℝ, x = univ.inf' hne π := ⟨_, rfl⟩
  have hπmin : 0 < πmin := hπmin_def ▸ (lt_inf'_iff _).2 fun a _ ↦ hπ.1 a
  have hπle : ∀ a, πmin ≤ π a := fun a ↦ hπmin_def ▸ inf'_le _ (mem_univ a)
  obtain ⟨θq, hθ0, hθhalf, hθα⟩ := exists_threshold hαN hπmin
  obtain ⟨θ, hθ⟩ : ∃ x : ℝ, x = θq := ⟨_, rfl⟩
  rw [← hθ] at hθ0 hθhalf hθα
  set m := Fintype.card (Reps M π) with hmdef
  obtain ⟨K₁, hK₁⟩ : ∃ x : ℝ, x = 512 * (m : ℝ) ^ 4 / (πmin / 2 * (2 * θ - θ) ^ 2 * (αN / 2) ^ 2) :=
    ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  obtain ⟨Sg, Kg, hSg, hK1, hKg⟩ := exists_grid_params m hαN (by positivity : 0 < πmin / 2)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨m * (2 * k + 2) * C + 2 + 2 * K₁ * (2 + k) + 2 * K₁ + 2,
    min (min (1 / (2 * k)) (πmin / (2 * C))) (min (αN / (4 * k)) (min ((θ / 2) ^ 2 / 2) (1 / 2))),
    by positivity, fun δ lam hδ0 hδc hl0 hlc ↦ ?_⟩
  -- the conditions on `δ` and `λ`
  have hδ1 : δ < 1 / (2 * k) := hδc.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ2 : δ < πmin / (2 * C) := hδc.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ3 : δ < αN / (4 * k) := hδc.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hl1 : lam < (θ / 2) ^ 2 / 2 :=
    hlc.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hl2 : lam < 1 / 2 :=
    hlc.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδk : k * δ < 1 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * k)).1 hδ1
    nlinarith
  have hδle1 : δ ≤ 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hδC : C * δ ≤ πmin / 2 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * C)).1 hδ2
    linarith
  have hδN : 2 * k * δ ≤ αN / 2 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * k)).1 hδ3
    linarith
  -- the parameters
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈32768 * (m : ℝ) ^ 2 / (αN ^ 2 * lam)⌉₊ + 1 := ⟨_, rfl⟩
  have hKge : 32768 * (m : ℝ) ^ 2 / (αN ^ 2 * lam) + 1 ≤ K := by
    rw [hK]
    push_cast
    linarith [Nat.le_ceil (32768 * (m : ℝ) ^ 2 / (αN ^ 2 * lam))]
  have hKpos : 0 < K := by rw [hK]; omega
  set T := ⌊1 + 4 / (θ / 2) ^ 4⌋₊ with hT
  refine ⟨((m, m, Sg, Kg, ((3 + 12 * K) ^ T + 1) ^ m + (2 * Kg + 1) ^ (m * m)),
    (T + 2 + K, T, (Nat.sqrt T + 1) * K, (3 + 12 * K) ^ T)), fun G hreg hexp hcol ↦ ?_⟩
  rw [← card_reps_eq M π]
  have h := isColoring_expAlg hM hπ hk hC hstab hαN hsepN hπmin hπle hθ0 (by linarith) hθα hδ0
    hδk hδC hδN hl0 (by linarith) hl1 hKpos le_rfl hSg hK1 hKg (Nat.le_add_right _ _)
    (Nat.le_add_left _ _) G hreg hexp hcol
  refine ⟨h.1, le_trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)) h.2⟩
  have hF := net_cost_le (m := m) hαN hl0 hKge
  have hE : 512 * (m : ℝ) ^ 4 * ((2 + k) * δ / lam + lam) /
      (πmin / 2 * (2 * θ - θ) ^ 2 * (αN / 2) ^ 2) = K₁ * ((2 + k) * δ / lam + lam) := by
    rw [hK₁, mul_div_right_comm]
  rw [hE]
  have := uncovered_le (m := m) (k := k) hC.le hK₁0 hδ0 hδle1 hl0 hF
  linarith

/-! ### The theorems -/

/-- **Theorem 1.9 (1)** of [BHSV25], full version (Theorem 7.1). -/
theorem expanderColoring_algorithm :
    ∃ C : ℕ, ∀ (k : ℕ) (M : Matrix (Fin k) (Fin k) ℝ) (π : Fin k → ℝ), IsModel M →
      IsStationary M π →
      ∃ B c₀ : ℝ, 0 < c₀ ∧ ∀ δ lam : ℝ, 0 ≤ δ → δ < c₀ → 0 < lam → lam < c₀ →
        ∃ K : ℝ, ∃ A : Graph → List ℕ, RunsInTime A encGraph encColoring K C ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.MColorable M δ →
            G.IsColoring (Nat.card (Set.range M))
              (alpha M π + B * (Real.sqrt δ + lam + δ / lam)) (A G) := by
  obtain ⟨C, hrun⟩ := exists_runsInTime_graph_fix
    (V := fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ expAlg z.1 z.2)
    expAlg_polytime
  refine ⟨C, fun k M π hM hπ ↦ ?_⟩
  obtain ⟨B, c₀, hc₀, h⟩ := exists_expAlg_params hM hπ
  refine ⟨B, c₀, hc₀, fun δ lam hδ0 hδc hl0 hlc ↦ ?_⟩
  obtain ⟨p, hp⟩ := h δ lam hδ0 hδc hl0 hlc
  obtain ⟨K, hK⟩ := hrun p
  exact ⟨K, _, hK, hp⟩

/-- **Theorem 1.8 (1)** of [BHSV25], full version (Corollary 7.2). -/
theorem expanderColoring_distinctRows :
    ∃ C : ℕ, ∀ (k : ℕ) (M : Matrix (Fin k) (Fin k) ℝ), IsModel M → Function.Injective M →
      ∃ B c₀ : ℝ, 0 < c₀ ∧ ∀ δ lam : ℝ, 0 ≤ δ → δ < c₀ → 0 < lam → lam < c₀ →
        ∃ K : ℝ, ∃ A : Graph → List ℕ, RunsInTime A encGraph encColoring K C ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.MColorable M δ →
            G.IsColoring k (B * (Real.sqrt δ + lam + δ / lam)) (A G) := by
  obtain ⟨C, hrun⟩ := exists_runsInTime_graph_fix
    (V := fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ expAlg z.1 z.2)
    expAlg_polytime
  refine ⟨C, fun k M hM hrows ↦ ?_⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- without colors only the empty graph is `(M, δ)`-colorable
    subst hk0
    refine ⟨0, 1, one_pos, fun δ lam _ _ _ _ ↦ ?_⟩
    obtain ⟨K, hK⟩ := hrun default
    refine ⟨K, _, hK, fun G _ _ hcol ↦ ?_⟩
    obtain ⟨χ, -⟩ := hcol
    have hn : G.1 = 0 := by
      by_contra h
      exact (χ ⟨0, Nat.pos_of_ne_zero h⟩).elim0
    refine ⟨fun u _ _ _ ↦ absurd u.2 (by omega), ?_⟩
    rw [hn, Nat.cast_zero, mul_zero]
    exact Nat.cast_nonneg _
  obtain ⟨π, hπ⟩ := exists_isStationary_of_ne_zero M hM hk.ne'
  obtain ⟨B, c₀, hc₀, h⟩ := exists_expAlg_params hM hπ
  refine ⟨B, c₀, hc₀, fun δ lam hδ0 hδc hl0 hlc ↦ ?_⟩
  obtain ⟨p, hp⟩ := h δ lam hδ0 hδc hl0 hlc
  obtain ⟨K, hK⟩ := hrun p
  have hcard : Nat.card (Set.range M) = k := by
    rw [Nat.card_range_of_injective hrows, Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨K, _, hK, fun G hreg hexp hcol ↦ ?_⟩
  have := hp G hreg hexp hcol
  rwa [hcard, alpha_eq_zero hπ.1 hrows, zero_add] at this

end Alg

end BHSV25
