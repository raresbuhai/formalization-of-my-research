module

public import BDT24.LowDeg.Spike
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

/-!
# The norm of the low-degree likelihood ratio

`BDT24.LowDeg.lowDegNorm_le`: the squared Hermite coefficients of the planted sample, summed
over `0 < |α| ≤ D`, are at most `∑_{L=1}^{⌊D/2⌋} (n + L)^L / L! · E ⟨x_u, x_v⟩^(2L)`, the bound the
paper takes from [Ding et al., Equations (8) and (10)].

The coefficient of `H_α` is the average over sign patterns `v` of `∏ᵢ hermCoef θ x_v αᵢ`, over the
rows `αᵢ` of `α` (`BDT24.LowDeg.integral_plantedSample`, `BDT24.LowDeg.integral_hermiteMv_planted`).
Squaring the average gives the average over pairs `(u, v)` of the product, and summing over the
rows with `|αᵢ| = 2mᵢ` gives `∏ᵢ θ^(2mᵢ) cₘᵢ ⟨x_u, x_v⟩^(2mᵢ)` with `cₘ = ((2m - 1)!!)² / (2m)! ≤ 1`
(`BDT24.LowDeg.sum_hermCoef_pair`; odd rows contribute `0`). With `θ ≤ 1`, the sum over
`(mᵢ)` with `0 < 2 ∑ mᵢ ≤ D` is at most `∑_L C(n + L - 1, L) ⟨x_u, x_v⟩^(2L)`, and
`C(n + L - 1, L) ≤ (n + L)^L / L!`.
-/

@[expose] public section

namespace BDT24.LowDeg

open MeasureTheory ProbabilityTheory

namespace NM

/-- `n‼ ≤ (n + 1)‼`. -/
theorem nmDoubleFact_le_succ : ∀ n : ℕ, n.doubleFactorial ≤ (n + 1).doubleFactorial
  | 0 => le_refl _
  | 1 => by decide
  | n + 2 => by
    rw [Nat.doubleFactorial_add_two, show n + 2 + 1 = (n + 1) + 2 by ring,
      Nat.doubleFactorial_add_two]
    exact Nat.mul_le_mul (by omega) (nmDoubleFact_le_succ n)

/-- `((2L - 1)‼)² ≤ (2L)!`. -/
theorem nmDoubleFact_sq_le (L : ℕ) :
    (2 * L - 1).doubleFactorial ^ 2 ≤ (2 * L).factorial := by
  rcases L with _ | l
  · simp
  · rw [show 2 * (l + 1) - 1 = 2 * l + 1 by omega, show 2 * (l + 1) = (2 * l + 1) + 1 by ring,
      Nat.factorial_eq_mul_doubleFactorial, sq]
    exact Nat.mul_le_mul_right _ (nmDoubleFact_le_succ _)

/-- The number of `μ : Fin n → ℕ` with `∑ μ = L` is at most `(n + L)^L / L!`. -/
theorem nmCard_antidiagonalTuple_le (n L : ℕ) :
    ((Finset.Nat.antidiagonalTuple n L).card : ℝ) ≤ ((n : ℝ) + L) ^ L / L.factorial := by
  have h : (Finset.Nat.antidiagonalTuple n L).card = (n + L - 1).choose L := by
    rw [← Finset.piAntidiag_univ_fin_eq_antidiagonalTuple]
    have := Finset.card_finsuppAntidiag_nat_eq_choose (s := (Finset.univ : Finset (Fin n))) L
    simpa [Finset.finsuppAntidiag] using this
  rw [h]
  calc ((n + L - 1).choose L : ℝ) ≤ ((n + L - 1 : ℕ) : ℝ) ^ L / L.factorial :=
        Nat.choose_le_pow_div L _
    _ ≤ ((n : ℝ) + L) ^ L / L.factorial := by
        gcongr
        have : ((n + L - 1 : ℕ) : ℝ) ≤ ((n + L : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
        simpa using this

/-- The pairing of the Hermite coefficients of two vectors over the multi-indices of degree
`t`. -/
noncomputable def nmRowMass {m : ℕ} (θ : ℝ) (x y : Fin m → ℝ) (t : ℕ) : ℝ :=
  ∑ b ∈ Finset.Nat.antidiagonalTuple m t, hermCoef θ x b * hermCoef θ y b / multiFact b

/-- Rows of odd degree contribute `0`. -/
theorem nmRowMass_odd {m : ℕ} (θ : ℝ) (x y : Fin m → ℝ) {t : ℕ} (ht : ¬ Even t) :
    nmRowMass θ x y t = 0 := by
  refine Finset.sum_eq_zero fun b hb ↦ ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at hb
  simp [hermCoef, hb, ht]

/-- Rows of degree `2L` contribute between `0` and `⟨x, y⟩^(2L)`. -/
theorem nmRowMass_even {m : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (x y : Fin m → ℝ) (L : ℕ) :
    0 ≤ nmRowMass θ x y (2 * L) ∧ nmRowMass θ x y (2 * L) ≤ (∑ j, x j * y j) ^ (2 * L) := by
  rw [nmRowMass, sum_hermCoef_pair]
  set s := ∑ j, x j * y j
  have hs : 0 ≤ s ^ (2 * L) := by rw [pow_mul]; positivity
  have hc1 : ((2 * L - 1).doubleFactorial : ℝ) ^ 2 / (2 * L).factorial ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast nmDoubleFact_sq_le L) (by positivity)
  have hθ : θ ^ (2 * L) ≤ 1 := pow_le_one₀ hθ0 hθ1
  refine ⟨by positivity, ?_⟩
  calc θ ^ (2 * L) * ((2 * L - 1).doubleFactorial : ℝ) ^ 2 / (2 * L).factorial * s ^ (2 * L)
      = θ ^ (2 * L) * (((2 * L - 1).doubleFactorial : ℝ) ^ 2 / (2 * L).factorial) *
          s ^ (2 * L) := by ring
    _ ≤ 1 * 1 * s ^ (2 * L) := by gcongr
    _ = s ^ (2 * L) := by ring

/-- Splitting the multi-indices `α` with `0 < |α| ≤ D` into their rows: the sum of a product
over the rows is the sum over the row degrees `e` of the product of the sums over each row. -/
theorem nmSum_rows {n m D : ℕ} (g : (Fin m → ℕ) → ℝ) :
    ∑ α ∈ (degSet (Fin n × Fin m) D).filter (· ≠ 0), ∏ i, g (fun j ↦ α (i, j)) =
      ∑ e ∈ (Finset.Icc 1 D).biUnion (Finset.Nat.antidiagonalTuple n),
        ∏ i, ∑ b ∈ Finset.Nat.antidiagonalTuple m (e i), g b := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun α i ↦ ∑ j, α (i, j))
    (t := (Finset.Icc 1 D).biUnion (Finset.Nat.antidiagonalTuple n))]
  · refine Finset.sum_congr rfl fun e he ↦ ?_
    rw [Finset.prod_univ_sum]
    refine Finset.sum_equiv (Equiv.curry _ _ _) (fun α ↦ ?_) (fun α _ ↦ rfl)
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.Nat.mem_antidiagonalTuple] at he
    obtain ⟨T, ⟨h1, h2⟩, h3⟩ := he
    simp only [Finset.mem_filter, degSet, Fintype.mem_piFinset, Finset.mem_range,
      Finset.Nat.mem_antidiagonalTuple, Equiv.curry_apply, Function.curry_apply]
    constructor
    · rintro ⟨-, rfl⟩ i
      rfl
    · intro h
      have hfun : (fun i ↦ ∑ j, α (i, j)) = e := funext h
      have hsum : ∑ ij, α ij = ∑ i, e i := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun i _ ↦ h i
      refine ⟨⟨⟨fun ij ↦ ?_, by omega⟩, ?_⟩, hfun⟩
      · have h4 : α ij ≤ ∑ j, α (ij.1, j) :=
          Finset.single_le_sum (f := fun j ↦ α (ij.1, j)) (fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_univ ij.2)
        have h5 : e ij.1 ≤ ∑ i, e i :=
          Finset.single_le_sum (f := e) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ ij.1)
        rw [h ij.1] at h4
        omega
      · rintro rfl
        simp only [Pi.zero_apply, Finset.sum_const_zero] at hsum
        omega
  · intro α hα
    simp only [Finset.mem_filter, degSet] at hα
    obtain ⟨⟨-, hD⟩, h0⟩ := hα
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.Nat.mem_antidiagonalTuple]
    refine ⟨∑ ij, α ij, ⟨?_, hD⟩, (Fintype.sum_prod_type _).symm⟩
    by_contra hlt
    exact h0 (funext fun ij ↦ (Finset.sum_eq_zero_iff.1 (by omega) ij (Finset.mem_univ _)))

/-- Only even row degrees contribute. -/
theorem nmSum_even {n D : ℕ} (G : ℕ → ℝ) (hG : ∀ t, ¬ Even t → G t = 0) :
    ∑ μ ∈ (Finset.Icc 1 (D / 2)).biUnion (Finset.Nat.antidiagonalTuple n), ∏ i, G (2 * μ i) =
      ∑ e ∈ (Finset.Icc 1 D).biUnion (Finset.Nat.antidiagonalTuple n), ∏ i, G (e i) := by
  refine Finset.sum_of_injOn (fun μ i ↦ 2 * μ i) ?_ ?_ ?_ ?_
  · intro μ _ μ' _ h
    funext i
    have := congrFun h i
    simp only at this
    omega
  · intro μ hμ
    simp only [Finset.coe_biUnion, Finset.coe_Icc, Set.mem_iUnion, Set.mem_Icc,
      Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple, exists_prop] at hμ ⊢
    obtain ⟨T, ⟨h1, h2⟩, h3⟩ := hμ
    refine ⟨2 * T, ⟨by omega, by omega⟩, ?_⟩
    rw [← Finset.mul_sum, h3]
  · intro e he hne
    by_contra hprod
    have hev : ∀ i, Even (e i) := fun i ↦ by
      by_contra h
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) (hG _ h))
    apply hne
    refine ⟨fun i ↦ e i / 2, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_Icc,
        Finset.Nat.mem_antidiagonalTuple] at he ⊢
      obtain ⟨T, ⟨h1, h2⟩, h3⟩ := he
      have hsum : ∑ i, e i = 2 * ∑ i, e i / 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ (Nat.two_mul_div_two_of_even (hev i)).symm
      exact ⟨∑ i, e i / 2, ⟨by omega, by omega⟩, rfl⟩
    · funext i
      exact Nat.two_mul_div_two_of_even (hev i)
  · intro μ _
    rfl

/-- Summing the even rows: with `0 ≤ G (2t) ≤ s^(2t)`, the sum over `μ` with `1 ≤ ∑ μ ≤ D/2` is at
most `∑_L (n + L)^L / L! · s^(2L)`. -/
theorem nmSum_bound {n D : ℕ} (G : ℕ → ℝ) (s : ℝ) (hG0 : ∀ t, 0 ≤ G (2 * t))
    (hG1 : ∀ t, G (2 * t) ≤ s ^ (2 * t)) :
    ∑ μ ∈ (Finset.Icc 1 (D / 2)).biUnion (Finset.Nat.antidiagonalTuple n), ∏ i, G (2 * μ i) ≤
      ∑ L ∈ Finset.Icc 1 (D / 2), ((n : ℝ) + L) ^ L / L.factorial * s ^ (2 * L) := by
  rw [Finset.sum_biUnion]
  · refine Finset.sum_le_sum fun L _ ↦ ?_
    calc ∑ μ ∈ Finset.Nat.antidiagonalTuple n L, ∏ i, G (2 * μ i)
        ≤ ∑ μ ∈ Finset.Nat.antidiagonalTuple n L, s ^ (2 * L) := by
          refine Finset.sum_le_sum fun μ hμ ↦ ?_
          calc ∏ i, G (2 * μ i) ≤ ∏ i, s ^ (2 * μ i) :=
                Finset.prod_le_prod₀ (fun i _ ↦ hG0 _) (fun i _ ↦ hG1 _)
            _ = s ^ (2 * L) := by
                rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum,
                  Finset.Nat.mem_antidiagonalTuple.1 hμ]
      _ = (Finset.Nat.antidiagonalTuple n L).card * s ^ (2 * L) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((n : ℝ) + L) ^ L / L.factorial * s ^ (2 * L) := by
          refine mul_le_mul_of_nonneg_right (nmCard_antidiagonalTuple_le n L) ?_
          rw [pow_mul]
          positivity
  · intro L _ L' _ hne
    exact Finset.disjoint_left.2 fun μ h1 h2 ↦ hne
      ((Finset.Nat.mem_antidiagonalTuple.1 h1).symm.trans (Finset.Nat.mem_antidiagonalTuple.1 h2))

/-- **One pair of spikes**: the sum over `0 < |α| ≤ D` of `∏ᵢ hermCoef θ x αᵢ hermCoef θ y αᵢ / αᵢ!`
over the rows `αᵢ` of `α` is at most `∑_L (n + L)^L / L! · ⟨x, y⟩^(2L)`. -/
theorem nmPair_le {n m D : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (x y : Fin m → ℝ) :
    ∑ α ∈ (degSet (Fin n × Fin m) D).filter (· ≠ 0),
        ∏ i, (hermCoef θ x (fun j ↦ α (i, j)) * hermCoef θ y (fun j ↦ α (i, j)) /
          multiFact (fun j ↦ α (i, j))) ≤
      ∑ L ∈ Finset.Icc 1 (D / 2),
        ((n : ℝ) + L) ^ L / L.factorial * (∑ j, x j * y j) ^ (2 * L) := by
  rw [nmSum_rows (fun b ↦ hermCoef θ x b * hermCoef θ y b / multiFact b)]
  change ∑ e ∈ (Finset.Icc 1 D).biUnion (Finset.Nat.antidiagonalTuple n),
    ∏ i, nmRowMass θ x y (e i) ≤ _
  rw [← nmSum_even (nmRowMass θ x y) (fun t ht ↦ nmRowMass_odd θ x y ht)]
  exact nmSum_bound _ _ (fun t ↦ (nmRowMass_even hθ0 hθ1 x y t).1)
    (fun t ↦ (nmRowMass_even hθ0 hθ1 x y t).2)

/-- The squared Hermite coefficient of the planted sample over `α!` is the average over pairs of
sign patterns of the products over the rows. -/
theorem nmCoef_sq {n d k : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (α : Fin n × Fin (d + 1) → ℕ) :
    (∫ ω, MvPolynomial.eval (sampleCoords ω) (hermiteMv α) ∂(plantedSample n d k θ)) ^ 2 /
        multiFact α =
      (∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k,
        ∏ i, (hermCoef θ (spikeVector k u) (fun j ↦ α (i, j)) *
          hermCoef θ (spikeVector k v) (fun j ↦ α (i, j)) / multiFact (fun j ↦ α (i, j)))) /
        ((spikeSigns d k).card : ℝ) ^ 2 := by
  have hfact : multiFact α = ∏ i, multiFact (fun j ↦ α (i, j)) := by
    simp only [multiFact]
    exact Fintype.prod_prod_type _
  rw [integral_plantedSample θ,
    Finset.sum_congr rfl fun v hv ↦ integral_hermiteMv_planted hθ0 hθ1 hv α, hfact, div_pow,
    div_right_comm, sq, Finset.sum_mul_sum, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]

end NM

/-- **The norm of the low-degree likelihood ratio** [BDT24, proof of Theorem B.4]. -/
theorem lowDegNorm_le {n d k : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (D : ℕ) :
    ∑ α ∈ (degSet (Fin n × Fin (d + 1)) D).filter (· ≠ 0),
        (∫ ω, MvPolynomial.eval (sampleCoords ω) (hermiteMv α) ∂(plantedSample n d k θ)) ^ 2 /
          multiFact α ≤
      ∑ L ∈ Finset.Icc 1 (D / 2), ((n : ℝ) + L) ^ L / L.factorial * overlapMoment d k L := by
  rw [Finset.sum_congr rfl fun α _ ↦ NM.nmCoef_sq hθ0 hθ1 α, ← Finset.sum_div,
    Finset.sum_comm]
  rw [Finset.sum_congr rfl fun u _ ↦ Finset.sum_comm]
  have hR : ∀ L, ((n : ℝ) + L) ^ L / L.factorial * overlapMoment d k L =
      (∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k,
        ((n : ℝ) + L) ^ L / L.factorial * spikeIP k u v ^ (2 * L)) /
        ((spikeSigns d k).card : ℝ) ^ 2 := by
    intro L
    rw [overlapMoment, mul_div_assoc', Finset.mul_sum]
    simp_rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun L _ ↦ hR L, ← Finset.sum_div]
  gcongr
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun u _ ↦ ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun v _ ↦ NM.nmPair_le hθ0 hθ1 _ _

end BDT24.LowDeg
