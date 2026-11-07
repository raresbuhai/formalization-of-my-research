module

public import BHSV25.BK.Basic
public import BHSV25.BK.Invariance
public import BHSV25.BK.Ensemble
public import BHSV25.BK.HyperReverse

/-!
# Proof of It Ain't Over Till It's Over

The probability form of Mossel, O'Donnell and Oleszkiewicz's "It Ain't Over Till It's Over"
[MOO10, Theorem 4.9] used by the reduction (`BHSV25.BK.Aint.itAintOverProb_main`, which is
`BHSV25.BK.ItAintOverProb` with the subcube map `BHSV25.BK.mix` written out): for `M ≥ 2` and
`ζ > 0` there are `δ > 0`, `K` and `τ > 0` such that every `g : {0,1}^R → [0,1]` with `E g ≤ 1/2`
and all degree-`K` influences of `2g - 1` below `τ` has average at least `1 - δ` on a random
subcube (free coordinates `{j : aⱼ = 0}`, `a` uniform in `[M]^R`) with probability at most `ζ`.

Proof (`BHSV25/BK/README.md`, Section 7), with `r = √(1 - 1/M)` and `k = 2M`:

* the subcube average is `F(z, a) = mlEval (smoothC r ĝ) U(z, a)` for the three-valued ensemble
  `U` (`BHSV25.BK.Aint.subcube_eq`), and `E_x ψ(T_r g(x))` is the same polynomial under uniform
  signs (`BHSV25.BK.Aint.mlEval_smoothC_bitVec`);
* the invariance principle (`BHSV25.BK.Aint.invariance_laws`) compares `E ψ(F)` and
  `E ψ(T_r g)` for the ramp `ψ` (`0` below `1 - 2δ`, `1` above `1 - δ`), using only the
  influences in degree `≤ K` (`cutoffInfluence K i (2g - 1) = 4 Infᵢ^{≤K}(ĝ)`);
* reverse hypercontractivity on the cube (`BHSV25.BK.Aint.few_high`) bounds
  `P[T_r g ≥ 1 - 2δ] ≤ (2^{k+1} δ)^{1/(k-1)} < ζ/2` for `δ = (ζ/2)^{k-1}/2^{k+2}`.

Reference: E. Mossel, R. O'Donnell, K. Oleszkiewicz, *Noise stability of functions with low
influences: invariance and optimality*, Annals of Mathematics 171 (2010), Theorem 4.9.
-/

@[expose] public section

namespace BHSV25.BK.Aint

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic

variable {R : ℕ}

/-! ### Influences of `2g - 1` -/

theorem coefficient_two_mul_sub_one (g : Cube (Fin R) → ℝ) {s : Cube (Fin R)}
    (hs : s ≠ fun _ ↦ false) :
    coefficient (fun x ↦ 2 * g x - 1) s = 2 * coefficient g s := by
  have hw : ∀ x : Cube (Fin R), walsh (fun _ ↦ false) x = 1 := by
    intro x; simp [walsh, bitSign]
  have h0 := walsh_orthogonality s (fun _ ↦ false)
  simp only [hw, mul_one, hs, ↓reduceIte] at h0
  unfold coefficient
  rw [Finset.mul_expect]
  have e : ∀ x, (2 * g x - 1) * walsh s x = 2 * (g x * walsh s x) - walsh s x := fun x ↦ by ring
  simp_rw [e]
  rw [Finset.expect_sub_distrib, h0, sub_zero]

theorem inflC_truncC_eq (n : ℕ) (i : Fin R) (g : Cube (Fin R) → ℝ) :
    inflC (truncC n (coefficient g)) i = cutoffInfluence n i g := by
  unfold inflC truncC cutoffInfluence
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases h1 : s i = true <;> by_cases h2 : sdeg s ≤ n <;> simp_all

theorem cutoffInfluence_two_mul_sub_one (n : ℕ) (i : Fin R) (g : Cube (Fin R) → ℝ) :
    cutoffInfluence n i (fun x ↦ 2 * g x - 1) = 4 * inflC (truncC n (coefficient g)) i := by
  rw [inflC_truncC_eq]
  unfold cutoffInfluence
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hs0 : s ≠ fun _ ↦ false := by
    intro h
    have := (Finset.mem_filter.mp hs).2.1
    rw [h] at this
    exact Bool.false_ne_true this
  rw [coefficient_two_mul_sub_one g hs0]
  ring

/-! ### The ramp -/

/-- The ramp `ψ`: `0` below `1 - 2δ`, `1` above `1 - δ`, linear in between. -/
noncomputable def ramp (δ t : ℝ) : ℝ := min 1 (max 0 ((t - (1 - 2 * δ)) / δ))

theorem continuous_ramp (δ : ℝ) : Continuous (ramp δ) := by
  unfold ramp
  fun_prop

theorem ramp_lip {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) : |ramp δ a - ramp δ b| ≤ 1 / δ * |a - b| := by
  unfold ramp
  have h1 : |min 1 (max 0 ((a - (1 - 2 * δ)) / δ)) - min 1 (max 0 ((b - (1 - 2 * δ)) / δ))| ≤
      |max 0 ((a - (1 - 2 * δ)) / δ) - max 0 ((b - (1 - 2 * δ)) / δ)| := by
    have := abs_min_sub_min_le_max (1 : ℝ) (max 0 ((a - (1 - 2 * δ)) / δ)) 1
      (max 0 ((b - (1 - 2 * δ)) / δ))
    rwa [sub_self, abs_zero, max_eq_right (abs_nonneg (max 0 ((a - (1 - 2 * δ)) / δ) -
      max 0 ((b - (1 - 2 * δ)) / δ)))] at this
  have h2 : |max 0 ((a - (1 - 2 * δ)) / δ) - max 0 ((b - (1 - 2 * δ)) / δ)| ≤
      |(a - (1 - 2 * δ)) / δ - (b - (1 - 2 * δ)) / δ| := by
    rw [max_comm 0, max_comm 0]
    exact abs_max_sub_max_le_abs _ _ _
  have h3 : |(a - (1 - 2 * δ)) / δ - (b - (1 - 2 * δ)) / δ| = 1 / δ * |a - b| := by
    rw [← sub_div, abs_div, abs_of_pos hδ]
    ring_nf
  linarith

theorem ind_le_ramp {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : ind (1 - δ ≤ t) ≤ ramp δ t := by
  unfold ramp
  by_cases h : 1 - δ ≤ t
  · rw [ind_of h]
    have : 1 ≤ (t - (1 - 2 * δ)) / δ := by
      rw [le_div_iff₀ hδ]; linarith
    rw [min_eq_left (le_max_of_le_right this)]
  · rw [ind_of_not h]
    exact le_min zero_le_one (le_max_left _ _)

theorem ramp_le_ind {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : ramp δ t ≤ ind (1 - 2 * δ ≤ t) := by
  unfold ramp
  by_cases h : 1 - 2 * δ ≤ t
  · rw [ind_of h]
    exact min_le_left _ _
  · rw [ind_of_not h]
    have : (t - (1 - 2 * δ)) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
    rw [max_eq_left this]
    exact min_le_right _ _

/-! ### The theorem -/

/-- **It Ain't Over Till It's Over** [MOO10, Theorem 4.9], probability form
(`BHSV25.BK.ItAintOverProb` with `BHSV25.BK.mix` written out). -/
theorem itAintOverProb_main :
    ∀ M : ℕ, 2 ≤ M → ∀ ζ : ℝ, 0 < ζ → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∃ τ : ℝ, 0 < τ ∧
      ∀ (R : ℕ) (g : Cube (Fin R) → ℝ), (∀ x, 0 ≤ g x ∧ g x ≤ 1) → (𝔼 x, g x) ≤ 1 / 2 →
        (∀ i, cutoffInfluence K i (fun x ↦ 2 * g x - 1) < τ) →
          (𝔼 z : Cube (Fin R), 𝔼 a : Fin R → Fin M,
            ind (1 - δ ≤ 𝔼 y : Cube (Fin R),
              g (fun j ↦ if (a j : ℕ) = 0 then y j else z j))) ≤ ζ := by
  intro M hM ζ hζ
  have hM0 : 0 < M := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = 2 * M := ⟨_, rfl⟩
  have hk2 : 2 ≤ k := by omega
  have hr0 := rM_pos hM
  have hr1 := rM_lt_one hM
  have hrk : rM M ≤ 1 - 1 / (k : ℝ) := by
    rw [hk]; push_cast; exact rM_le hM
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (ζ / 2) ^ (k - 1) / 2 ^ (k + 2) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  obtain ⟨n, τ, hτ, hinv⟩ := invariance_laws (M := 1) (K := 1 / δ) hr0 hr1 (half_pos hζ)
  refine ⟨δ, hδ0, n, 4 * τ, by positivity, ?_⟩
  intro R g hg hmean hinf
  -- the hypotheses of the invariance principle
  have hc : ∑ s, coefficient g s ^ 2 ≤ 1 := by
    rw [walsh_parseval]
    refine Finset.expect_le Finset.univ_nonempty fun x _ ↦ ?_
    nlinarith [hg x]
  have hinfl : ∀ i, inflC (truncC n (coefficient g)) i ≤ τ := fun i ↦ by
    have := hinf i
    rw [cutoffInfluence_two_mul_sub_one] at this
    linarith
  have hlip : LipPair (fun a _ ↦ ramp δ a) (1 / δ) := by
    intro a b a' b'
    have := ramp_lip hδ0 a a'
    have : 0 ≤ 1 / δ * |b - b'| := by positivity
    simp only
    nlinarith
  have hI := hinv (law3 M) signLaw (goodLaw_law3 hM) goodLaw_signLaw R (coefficient g)
    (coefficient g) hc hc hinfl hinfl (fun a _ ↦ ramp δ a) hlip
  -- the two sides
  have hcont :
      Continuous (fun y : Fin R → ℝ ↦ ramp δ (mlEval (smoothC (rM M) (coefficient g)) y)) :=
    (continuous_ramp δ).comp (MultilinearGauss.continuous_mlEval' _)
  rw [← expect_eq_integral_law3 hM0 _ hcont, ← Lindeberg.expect_eq_integral_sign _ hcont] at hI
  simp_rw [← subcube_eq hM g, mlEval_smoothC_bitVec] at hI
  -- reverse hypercontractivity
  have hfew := few_high hk2 hr0.le hrk (by positivity : (0 : ℝ) ≤ 2 * δ) g
    (fun x ↦ ind (1 - 2 * δ ≤ noise (rM M) g x)) hg hmean
    (fun x ↦ ⟨ind_nonneg _, ind_le_one _⟩)
    (fun x hx ↦ by
      by_contra h
      exact hx (ind_of_not h))
  have hsmall : (𝔼 x, ind (1 - 2 * δ ≤ noise (rM M) g x)) ≤ ζ / 2 := by
    by_contra hcon
    push Not at hcon
    have h1 : (ζ / 2) ^ (k - 1) ≤ (𝔼 x, ind (1 - 2 * δ ≤ noise (rM M) g x)) ^ (k - 1) :=
      pow_le_pow_left₀ (by positivity) hcon.le _
    have h2 : (2 : ℝ) ^ k * (2 * δ) = (ζ / 2) ^ (k - 1) / 2 := by
      rw [hδ, pow_add]
      field_simp
    have h3 : 0 < (ζ / 2) ^ (k - 1) := by positivity
    linarith
  -- the chain
  calc (𝔼 z : Cube (Fin R), 𝔼 a : Fin R → Fin M,
        ind (1 - δ ≤ 𝔼 y : Cube (Fin R), g (fun j ↦ if (a j : ℕ) = 0 then y j else z j)))
      ≤ 𝔼 z : Cube (Fin R), 𝔼 a : Fin R → Fin M,
          ramp δ (𝔼 y : Cube (Fin R), g (fun j ↦ if (a j : ℕ) = 0 then y j else z j)) :=
        Finset.expect_le_expect fun z _ ↦ Finset.expect_le_expect fun a _ ↦ ind_le_ramp hδ0 _
    _ ≤ (𝔼 x, ramp δ (noise (rM M) g x)) + ζ / 2 := by
        have := (abs_le.mp hI).2
        linarith
    _ ≤ (𝔼 x, ind (1 - 2 * δ ≤ noise (rM M) g x)) + ζ / 2 := by
        gcongr with x
        exact ramp_le_ind hδ0 _
    _ ≤ ζ := by linarith

end BHSV25.BK.Aint
