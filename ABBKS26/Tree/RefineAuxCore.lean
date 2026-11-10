module

public import ABBKS26.Tree.RefineAuxPartition
public import Mathlib.Algebra.Order.Chebyshev
public import ABBKS26.Tree.RefineAuxIdMoments
public import ABBKS26.Tree.RefineAuxCleanData
public import ABBKS26.Tree.RefineAuxGrids
public import ABBKS26.Tree.RefineAuxUniform

/-!
# One refinement step

[ABBKS26, Algorithms 3 and 5] (`refine_spec`): robust isotropic position, Frobenius
clustering, the subspace theorem and the spectral or mean splits at one node. Window
verification is used only inside Frobenius clustering, to keep its list of splits small.
-/

@[expose] public section

namespace ABBKS26.Tree

noncomputable section


open Matrix

open Common
open scoped BigOperators
variable {n k d : ℕ}

def leakageBudget (params : ℕ → StepParams) (η : ℝ) (h : ℕ) : ℝ :=
  ((List.range h).map fun j ↦ (params j).straddle + 8 * η).sum

def stepBranchCap (mode : Mode) (k : ℕ) (p : StepParams) : ℕ :=
  let β := p.subspaceAccuracy
  match mode with
  | .centered => frobCap k +
      netBound (Centered.dimensionCap (p.w / 2)
        (10000 * p.sigmaSq / (p.w / 2) + 10) β) β *
          (Nat.clog 2 ⌈256 * (4 / p.w) ^ 2 / β ^ 2⌉₊ + 5)
  | .identical => netBound (IdCov.N_pack β k) β * (2 * ⌈64 * k * sqrtUp (1 / p.w)⌉₊ + 3)

def branchCap (mode : Mode) (k : ℕ) (params : ℕ → StepParams) : ℕ :=
  max 1 (k * ((List.range (k - 1)).map fun h ↦ stepBranchCap mode k (params h)).foldl max 0)

/-- The local rounder pays for rational accuracy bits as well as numerical sizes. -/
def idReserve (k : ℕ) (p : StepParams) : ℕ :=
  p.subspaceAccuracy.den + ⌈8 / p.w⌉₊ + IdCov.tDegree p.w +
    IdCov.N_pack p.subspaceAccuracy k + 100

def idReserves (k : ℕ) (params : ℕ → StepParams) : ℕ :=
  (((List.range (k - 1)).map fun h ↦ idReserve k (params h) + 2).prod + 2)

def localBudget (mode : Mode) (k n d : ℕ) (params : ℕ → StepParams) : ℕ :=
  (branchCap mode k params + 1) ^ (k + 1) *
    (n + d + 2) ^ (1000000000 * (Rounding.solverConstant + 1)) *
      (if mode = .centered then 1 else
        (d + 2) ^ (1000000000 * (Rounding.solverConstant + 1) *
          (logInv (params 0).w + 3) ^ 2) *
          (idReserves k params + 2) ^ (1000000000 * (Rounding.solverConstant + 1) *
            (logInv (params 0).w + 3) ^ 2))

/-- Numerical SCH obligations consumed by one refinement, with no success predicate inside. -/
def StepReady (mode : Mode) (k : ℕ) (p next : StepParams) : Prop :=
  0 < p.w ∧ p.w ≤ 1 / 2 ∧ 0 < p.subspaceAccuracy ∧
    p.subspaceAccuracy ≤ 1 / 100 ∧ 0 < p.straddle ∧ 0 < p.tail ∧
    p.straddle = next.leakage / 4 ∧ p.leakage ≤ next.leakage / 4 ∧
    p.leakage ≤ p.w * p.contamination / 128 ∧
    p.leakage ≤ p.w * p.windowMass / 1024 ∧
    p.verifyMass = p.w * p.windowMass / 8 ∧
    p.tail ≤ min (p.straddle / 64) (min (p.verifyMass / 64) (p.w / 4096)) ∧
    p.sigmaSq = 600 / (p.w / 2) ^ 2 + 2 * p.R ^ 2 ∧
    p.contamination ≤ min (1 / (64000 * p.sigmaSq))
      (min (p.w / 800) (min (p.isotropy ^ 2 / (10 ^ 10 * p.sigmaSq))
        (min (p.verifyMass / 64) (min (p.straddle / 64)
          (min (p.w / 4096) (p.w ^ 2 / 10 ^ 8)))))) ∧
    0 < p.frameAccuracy ∧ p.frameAccuracy ≤ p.isotropy / 10000 ∧
    match mode with
    | .centered =>
      p.windowMass = 1 / 2 ∧ 32 / p.straddle ≤ p.K ∧
      8 * (40 / p.w) * sqrtUp (1 / p.straddle) ≤ p.WF ∧
      4 * p.WF ≤ p.DF ∧ 4 * (40 / p.w) ^ 2 ≤ p.tail * p.DF ^ 2 ∧
      2 * (k - 1 : ℚ) * (2 * p.DF + 3 * p.WF) + 1 ≤ p.R ∧
      p.subspaceAccuracy ≤ 1 / (128 * (4 / p.w)) ∧
      p.subspaceAccuracy ≤ (128 * (4 / p.w))⁻¹ *
        (p.tail / (1024 * p.K ^ 2)) ^ (2 * (k - 1)) ∧
      p.isotropy = Centered.gammaStar (p.w / 2) p.subspaceAccuracy ∧
      p.momentError = Centered.etaStar (p.w / 2) p.subspaceAccuracy ∧
      p.contamination ≤ p.momentError / (10000 * (2 * (80 / p.w) ^ 4)) ∧
      (4 / p.w : ℝ) < (p.separation : ℝ) ^ 2 * 3 * p.subspaceAccuracy ^ 8 ∧
      (2 * Real.sqrt (10000 * (p.sigmaSq : ℝ) / (p.w / 2) + 10)) * (4 / p.w) ≤
        9 * p.separation * p.subspaceAccuracy ^ 16
    | .identical =>
      p.windowMass = (1 / (16 * k : ℚ)) * (p.straddle / 2) ^ 9 / 16 ∧
      40 / (p.w / 2) ^ 2 ≤ p.R ^ 2 ∧
      200 * (k : ℚ) ^ 2 * p.subspaceAccuracy ^ 2 ≤ p.tail ∧
      p.isotropy = IdCov.gammaStar p.subspaceAccuracy ∧
      p.momentError = IdCov.etaStar p.w p.subspaceAccuracy / 4 ∧
      p.contamination ≤ p.momentError /
        (10000 * (2 * (80 * IdCov.tDegree p.w / p.w) ^ (4 * IdCov.tDegree p.w))) ∧
      16 ≤ p.separation ^ 2 * p.w * IdCov.tauStar p.subspaceAccuracy

private theorem stepReady_isotropy_le_one (mode : Mode) (k : ℕ) (p next : StepParams)
    (hp : StepReady mode k p next) : p.isotropy ≤ 1 := by
  obtain ⟨hw, hw2, hβ, hβ100, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := hp
  have hβ1 : p.subspaceAccuracy ≤ 1 := hβ100.trans (by norm_num)
  cases mode with
  | centered =>
    obtain ⟨_, _, _, _, _, _, _, _, hγ, _⟩ := hm
    rw [hγ]
    have hw1 : p.w / 2 ≤ 1 := by linarith only [hw2]
    have hν : Centered.nu (p.w / 2) p.subspaceAccuracy ≤ 1 := by
      calc
        _ ≤ p.w / 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hβ.le hβ1) (by positivity)
        _ ≤ 1 := by simpa only [mul_one] using hw1
    have hν0 : 0 ≤ Centered.nu (p.w / 2) p.subspaceAccuracy := by
      unfold Centered.nu
      positivity
    have hδ := pow_le_one₀ hν0 hν (n := 8)
    have hδ0 := pow_nonneg hν0 8
    have hγ := pow_le_one₀ hδ0 hδ (n := 2)
    change Centered.delta (p.w / 2) p.subspaceAccuracy ^ 2 ≤ 1 at hγ
    change Centered.delta (p.w / 2) p.subspaceAccuracy ^ 2 / 20 ≤ 1
    linarith only [hγ]
  | identical =>
    obtain ⟨_, _, _, hγ, _⟩ := hm
    rw [hγ]
    have hβ25 : p.subspaceAccuracy / 25 ≤ 1 := by linarith only [hβ1]
    have hpow := pow_le_one₀ (div_nonneg hβ.le (by norm_num)) hβ25 (n := 8)
    change (p.subspaceAccuracy / 25) ^ 8 / 6 ≤ 1
    linarith only [hpow]

def Prepared (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams) : Prop :=
  M.Valid ∧ mode.Condition M ∧ mode.Separated M Δ ∧
    0 < w ∧ (∀ j, w ≤ M.w j) ∧ 0 ≤ ε ∧ 0 < η ∧ η ≤ 1 / 100 ∧
    (match mode with
      | .centered => 8
      | .identical => 8 * IdCov.tDegree (params 0).w) ≤ D ∧
    Good M ε w η D ω ∧ IsRounding M (1 / n) r ∧
    sampleNeed w η (1 / 2) k d D ≤ n ∧
    10 ^ 10 ≤ w * n / 4 ∧
    (params (k - 1)).contamination ≤ 2 / 10 ^ 10 ∧
    (∀ h, h < k - 1 → StepReady mode k (params h) (params (h + 1))) ∧
    ∀ h, h < k → ((params h).w : ℝ) = w ∧
      leakageBudget params η h ≤ (params h).leakage ∧
      8 * ((params h).leakage + ε + η + 1 / n) / w ≤ (params h).contamination ∧
      0 ≤ (params h).separation ∧
      (params h).separation ≤ Δ ∧
      η ≤ ((params h).frameAccuracy : ℝ) ^ 2 ∧
      (h < k - 1 → SoundConditions (params h) ε η (leakageBudget params η h))

private theorem separated_mono (mode : Mode) (M : Mixture k d) (δ Δ : ℝ)
    (hM : M.Valid) (hδ : 0 ≤ δ) (hle : δ ≤ Δ) (hs : mode.Separated M Δ) :
    mode.Separated M δ := by
  have hsq : δ ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ hδ hle 2
  have hcov (j : Fin k) (v : Vec d) : 0 ≤ v ⬝ᵥ (M.S j *ᵥ v) :=
    (hM.posDef j).posSemidef.dotProduct_mulVec_nonneg v
  cases mode with
  | centered =>
    intro a b hab
    rcases hs a b hab with ⟨v, hv⟩ | ⟨v, hv⟩ | ⟨t, ht, hv⟩ | ⟨t, ht, hv⟩
    · exact Or.inl ⟨v, (mul_le_mul_of_nonneg_right hsq (hcov b v)).trans_lt hv⟩
    · exact Or.inr (Or.inl
        ⟨v, (mul_le_mul_of_nonneg_right hsq (hcov a v)).trans_lt hv⟩)
    · exact Or.inr (Or.inr (Or.inl
        ⟨t, ht, (mul_le_mul_of_nonneg_right hsq (sq_nonneg t)).trans_lt hv⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨t, ht, (mul_le_mul_of_nonneg_right hsq (sq_nonneg t)).trans_lt hv⟩))
  | identical =>
    intro a b hab
    obtain ⟨v, hv⟩ := hs a b hab
    exact ⟨v, (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq (by norm_num)) (hcov a v)).trans_lt hv⟩

theorem Prepared.separated_at
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k) :
    mode.Separated M (params h).separation := by
  obtain ⟨hM, _, hs, _, _, _, _, _, _, _, _, _, _, _, _, hparams⟩ := hp
  obtain ⟨_, _, _, hnonneg, hle, _⟩ := hparams h hh
  exact separated_mono mode M _ Δ hM (by exact_mod_cast hnonneg) hle hs

/-- The moment budget is sufficient at every depth, since all step weights agree. -/
theorem Prepared.moment_degree_at
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k) :
    (match mode with
      | .centered => 8
      | .identical => 8 * IdCov.tDegree (params h).w) ≤ D := by
  obtain ⟨_, _, _, _, _, _, _, _, hD, _, _, _, _, _, _, hparams⟩ := hp
  have hw : (params h).w = (params 0).w := by
    apply Rat.cast_injective (α := ℝ)
    exact (hparams h hh).1.trans (hparams 0 (by omega)).1.symm
  cases mode <;> simpa only [hw] using hD

/-- Both modes supply the eighth moments needed by the robust frame procedure. -/
theorem Prepared.eight_le_degree
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) : 8 ≤ D := by
  obtain ⟨_, _, _, _, _, _, _, _, hD, _⟩ := hp
  cases mode with
  | centered => exact hD
  | identical =>
    change 8 * (logInv (params 0).w + 3) ≤ D at hD
    omega

theorem Prepared.weight_at
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k) :
    ((params h).w : ℝ) = w := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hparams⟩ := hp
  exact (hparams h hh).1

private theorem leakageBudget_succ (params : ℕ → StepParams) (η : ℝ) (h : ℕ) :
    leakageBudget params η (h + 1) =
      leakageBudget params η h + (params h).straddle + 8 * η := by
  simp only [leakageBudget, List.range_succ, List.map_append, List.map_singleton,
    List.sum_append, List.sum_singleton, add_assoc]

theorem Prepared.leakageBudget_le_succ
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1) :
    leakageBudget params η h ≤ leakageBudget params η (h + 1) := by
  obtain ⟨_, _, _, _, _, _, hη, _, _, _, _, _, _, _, hready, _⟩ := hp
  obtain ⟨_, _, _, _, hφ, _⟩ := hready h hh
  have hφ' : (0 : ℝ) < (params h).straddle := by exact_mod_cast hφ
  rw [leakageBudget_succ]
  linarith

theorem Prepared.leakageBudget_nonneg
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k) :
    0 ≤ leakageBudget params η h := by
  obtain ⟨_, _, _, _, _, _, hη, _, _, _, _, _, _, _, hready, _⟩ := hp
  unfold leakageBudget
  apply List.sum_nonneg
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
  have hjh := List.mem_range.mp hj
  have hφ := (hready j (by omega)).2.2.2.2.1
  have hφR : (0 : ℝ) < (params j).straddle := by exact_mod_cast hφ
  positivity

private theorem prepared_rounding_bound
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) :
    (2 * radius d η + 2) / η ≤ n := by
  obtain ⟨_, _, _, _, _, _, hη, hη100, _, _, _, hn, _⟩ := hp
  have hsample : 32 * (d + 1 : ℝ) / η ^ 2 ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hη1 : η ≤ 1 := by linarith only [hη100]
  have hs := Real.sq_sqrt (div_nonneg (Nat.cast_nonneg d) hη.le)
  have hroot : η * Real.sqrt (d / η) ≤ d + 1 := by
    have hsq : (η * Real.sqrt (d / η)) ^ 2 = η * d := by
      rw [mul_pow, hs]
      field_simp
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hηd : η * d ≤ d := mul_le_of_le_one_left hd hη1
    have hnonneg : 0 ≤ η * Real.sqrt (d / η) := by positivity
    nlinarith only [hsq, hηd, hd, hnonneg, sq_nonneg (d : ℝ)]
  have hnum : (2 * radius d η + 2) * η ≤ 32 * (d + 1 : ℝ) := by
    unfold radius
    nlinarith only [hroot, hη1, Nat.cast_nonneg (α := ℝ) d]
  apply le_trans ?_ hsample
  rw [div_le_div_iff₀ hη (sq_pos_of_pos hη)]
  nlinarith only [mul_le_mul_of_nonneg_right hnum hη.le]

/-- A good block meets the scheduled contamination tolerance of its depth. -/
theorem Prepared.contamination_at
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hl : leakage ω N I ≤ leakageBudget params η h) (hN : w * n / 4 ≤ N.card) :
    nodeContamination ω N I ≤ (params h).contamination := by
  obtain ⟨hM, _, _, hw, hwj, _, hη, hη100, _, hg, _, _, _, _, _, hparams⟩ := hp
  obtain ⟨_, hleak, hcont, _⟩ := hparams h hh
  apply (contamination_bound M ε w η (params h).leakage D ω N I hg hM hw hwj
    ⟨hη.le, hη100⟩ hI (hl.trans hleak) hN).trans hcont

private theorem prepared_eta_contamination
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1) :
    8 * η ≤ (params h).contamination := by
  have hl := hp.leakageBudget_nonneg mode M ε w η Δ D ω r params h (by omega)
  have hwcast := hp.weight_at mode M ε w η Δ D ω r params h (by omega)
  obtain ⟨_, _, _, hw, _, hε, hη, _, _, _, _, _, _, _, hready, hparams⟩ := hp
  obtain ⟨_, hw2, _⟩ := hready h hh
  have hw1 : w ≤ 1 := by
    have hwR := Rat.cast_le (K := ℝ) |>.mpr hw2
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hwR
    linarith only [hwR, hwcast]
  obtain ⟨_, hleak, hc, _⟩ := hparams h (by omega)
  have hleak0 : (0 : ℝ) ≤ (params h).leakage := hl.trans hleak
  have he := (div_le_iff₀ hw).mp hc
  have hn : (0 : ℝ) ≤ 1 / n := by positivity
  have hc0 : (0 : ℝ) ≤ (params h).contamination := by
    have hnum : 0 ≤ 8 * ((params h).leakage + ε + η + 1 / n) / w := by positivity
    exact hnum.trans hc
  have hm := mul_le_mul_of_nonneg_left hw1 hc0
  linarith only [he, hm, hleak0, hε, hn]

/-- The rounded node reference is resilient through every required positive even degree. -/
theorem Prepared.reference_resilient_at
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty)
    (s : ℕ) (hs0 : 0 < s) (hs : s ≤ D) (heven : Even s) :
    (ABBKS26.RefineAux.roundedReference M ω r N I hI).Resilient s (η / 10 ^ 8) := by
  have hD := hp.eight_le_degree mode M ε w η Δ D ω r params
  obtain ⟨hM, _, _, hw, hwj, _, hη, hη100, _, hg, hr, hn, _⟩ := hp
  apply ABBKS26.RefineAux.roundedReference_resilient M ω r N I hI hM s _ (by positivity)
  intro j _ q hq
  exact ABBKS26.RefineAux.Resilience.rounded_moments_scheduled M ε w η D ω r
    hM hg hr hw hwj hη hη100 hD hn j s hs0 hs heven q hq

/-- The robust reference is valid for the actual rounded clean points and empirical weights. -/
theorem Prepared.reference_valid_at
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty) :
    (ABBKS26.RefineAux.roundedReference M ω r N I hI).Valid (w / 2) := by
  have hD := hp.eight_le_degree mode M ε w η Δ D ω r params
  have hres := hp.reference_resilient_at mode M ε w η Δ D ω r params N I hI 4
    (by omega) (by omega) (by decide)
  obtain ⟨hM, _, _, hw, hwj, _, hη, hη100, _, hg, _⟩ := hp
  apply ABBKS26.RefineAux.roundedReference_valid M ε w η D ω r N I hI hM hg hw hwj
    ⟨hη.le, hη100⟩
  apply ABBKS26.RefineAux.reference_cov_posDef _ (fun j ↦ hM.posDef _) _ _
    ⟨by positivity, by linarith only [hη100]⟩ hres
  let j := hI.choose
  have hj : j ∈ I := hI.choose_spec
  have hne := Finset.card_pos.mp (SoundAux.good_cluster_pos M ε w η D ω hg j)
  apply hne.mono
  intro l hl
  have hl' : (ω l).1 = j := (Finset.mem_filter.mp hl).2
  change l ∈ referenceSet ω I
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl' ▸ hj⟩


private theorem prepared_loop_hypotheses
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hl : leakage ω N I ≤ leakageBudget params η h) (hN : w * n / 4 ≤ N.card) :
    let p := params h
    let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
    R.Valid (((p.w / 2 : ℚ) : ℝ)) ∧ R.Resilient 4 (1 / 10000) ∧
      ((p.w / 2 : ℚ) : ℝ) ≤ 1 ∧ 0 < ((p.isotropy / 10000 : ℚ) : ℝ) ∧
      R.contamination ≤ min
        (Robust.maxContamination ((p.w / 2 : ℚ) : ℝ) (|p.R| : ℚ))
        (((p.w / 2 : ℚ) : ℝ) / 400) := by
  let p := params h
  let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
  have hweight := hp.weight_at mode M ε w η Δ D ω r params h (by omega)
  have hv := hp.reference_valid_at mode M ε w η Δ D ω r params N I hI
  have hres := hp.reference_resilient_at mode M ε w η Δ D ω r params N I hI 4
    (by omega) ((by omega : 4 ≤ 8).trans
      (hp.eight_le_degree mode M ε w η Δ D ω r params)) (by decide)
  have hc := hp.contamination_at mode M ε w η Δ D ω r params h (by omega)
    N I hI hl hN
  change R.contamination ≤ (p.contamination : ℝ) at hc
  obtain ⟨_, _, _, _, _, _, _, hη100, _, _, _, _, _, _, hready, _⟩ := hp
  obtain ⟨hw, hw2, _, _, _, _, _, _, _, _, _, _, hσ, hreq, hζ, hζle, _⟩ :=
    hready h hh
  have hσeq : p.sigmaSq = 600 / (p.w / 2) ^ 2 + 2 * p.R ^ 2 := hσ
  have hreqσ := hreq.trans (min_le_left _ _)
  have hreqw := hreq.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hv' : R.Valid ((p.w / 2 : ℚ) : ℝ) := by
    rw [Rat.cast_div, Rat.cast_ofNat, hweight]
    exact hv
  refine ⟨hv', ?_, ?_, ?_, ?_⟩
  · apply ABBKS26.RefineAux.resilient_tolerance_mono R 4 _ _ hres
    linarith only [hη100]
  · have hhQ : p.w / 2 ≤ 1 := by linarith only [hw2]
    exact_mod_cast hhQ
  · have hpos : 0 < p.isotropy / 10000 := by linarith only [hζ, hζle]
    exact_mod_cast hpos
  · apply le_min
    · apply hc.trans
      unfold Robust.maxContamination
      rw [ABBKS26.RefineAux.frame_sigmaSq p hσeq]
      exact_mod_cast hreqσ
    · apply hc.trans
      have hhR := Rat.cast_le (K := ℝ) |>.mpr hreqw
      push_cast at hhR ⊢
      simpa only [div_div, show (2 : ℝ) * 400 = 800 by norm_num] using hhR


/-- The scheduled contamination makes the clean-pass normalization error small. -/
theorem Prepared.close_frame_error_at
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hl : leakage ω N I ≤ leakageBudget params η h) (hN : w * n / 4 ≤ N.card)
    (F : Robust.FrameResult d)
    (hF : Robust.CloseFrame (ABBKS26.RefineAux.roundedReference M ω r N I hI) F
      (((params h).w / 2 : ℚ) : ℝ) (|(params h).R| : ℚ)
        (((params h).isotropy / 10000 : ℚ) : ℝ)) :
    frobSq (F.transform.map (algebraMap ℚ ℝ) *
      (ABBKS26.RefineAux.roundedReference M ω r N I hI).cov *
        (F.transform.map (algebraMap ℚ ℝ))ᵀ - 1) ≤
      (((params h).isotropy : ℝ) / 1000) ^ 2 := by
  let p := params h
  let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
  have hc := hp.contamination_at mode M ε w η Δ D ω r params h (by omega)
    N I hI hl hN
  change R.contamination ≤ (p.contamination : ℝ) at hc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hr, _⟩ := hp
  obtain ⟨hw, hw2, _, _, _, _, _, _, _, _, _, _, hσeq, hreq, hζ, hζle, _⟩ := hr h hh
  change p.sigmaSq = 600 / (p.w / 2) ^ 2 + 2 * p.R ^ 2 at hσeq
  have hσ1 := ABBKS26.RefineAux.sigmaSq_one_le p hw hw2 hσeq
  have hσpos : (0 : ℝ) < p.sigmaSq := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hσ1)
  have hγ : (0 : ℝ) < p.isotropy := by
    have hγQ : 0 < p.isotropy := by linarith only [hζ, hζle]
    exact_mod_cast hγQ
  have hreqγ := hreq.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hbudget : (p.contamination : ℝ) * (10 ^ 10 * p.sigmaSq) ≤
      (p.isotropy : ℝ) ^ 2 := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ 10 * p.sigmaSq)).mp
    exact_mod_cast hreqγ
  have hσid := ABBKS26.RefineAux.frame_sigmaSq p hσeq
  have hcont0 := ABBKS26.RefineAux.contamination_nonneg R
  have hprod : Real.sqrt (p.sigmaSq : ℝ) *
      Real.sqrt R.contamination ≤ (p.isotropy : ℝ) / 100000 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hσpos.le, Real.sq_sqrt hcont0]
    have hm := mul_le_mul_of_nonneg_left hc hσpos.le
    nlinarith only [hm, hbudget]
  apply hF.2.trans
  change (65 * Real.sqrt (Robust.sigmaSq ((p.w / 2 : ℚ) : ℝ) (|p.R| : ℚ)) *
    Real.sqrt R.contamination + ((p.isotropy / 10000 : ℚ) : ℝ)) ^ 2 ≤ _
  rw [hσid]
  push_cast
  apply pow_le_pow_left₀ (by positivity)
  linarith only [hprod, hγ]

/-- The clean-pass transform is nonsingular and normalizes every population covariance. -/
theorem Prepared.frame_population_cov_at
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hl : leakage ω N I ≤ leakageBudget params η h) (hN : w * n / 4 ≤ N.card)
    (F : Robust.FrameResult d)
    (hF : Robust.CloseFrame (ABBKS26.RefineAux.roundedReference M ω r N I hI) F
      (((params h).w / 2 : ℚ) : ℝ) (|(params h).R| : ℚ)
        (((params h).isotropy / 10000 : ℚ) : ℝ)) :
    let T := F.transform.map (algebraMap ℚ ℝ)
    let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
    T.det ≠ 0 ∧ ∀ j, LE (T * R.model.cov j * Tᵀ)
      ((1.1 / (w / 2)) • (1 : Mat d)) := by
  let T := F.transform.map (algebraMap ℚ ℝ)
  let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
  have hvalid := hp.reference_valid_at mode M ε w η Δ D ω r params N I hI
  have hres := hp.reference_resilient_at mode M ε w η Δ D ω r params N I hI 4
    (by omega) ((by omega : 4 ≤ 8).trans
      (hp.eight_le_degree mode M ε w η Δ D ω r params)) (by decide)
  have herr := hp.close_frame_error_at mode M ε w η Δ D ω r params h hh N I hI hl hN F hF
  obtain ⟨_, _, _, _, _, _, hη, hη100, _, _, _, _, _, _, hready, _⟩ := hp
  have hγ : ((params h).isotropy : ℝ) ≤ 1 := by
    exact_mod_cast stepReady_isotropy_le_one mode k _ _ (hready h hh)
  have hγ0 : (0 : ℝ) ≤ (params h).isotropy := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hζ, hζle, _⟩ := hready h hh
    have hγQ : 0 < (params h).isotropy := by linarith only [hζ, hζle]
    exact_mod_cast hγQ.le
  have he : frobSq (T * R.cov * Tᵀ - 1) ≤ (1 / 100 : ℝ) ^ 2 := by
    apply herr.trans
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hγ]
  obtain ⟨hT, hcov⟩ := ABBKS26.RefineAux.empirical_frame_bounds R.cov T
    hvalid.2.2.2.2.2.1.posSemidef he
  refine ⟨hT, ?_⟩
  exact ABBKS26.RefineAux.population_component_cov_bound R T (w / 2) (η / 10 ^ 8)
    hvalid ⟨by positivity, by linarith only [hη100]⟩ hres hcov

/-- The centered clean-pass frame meets the population isotropy tolerance of Theorem Z. -/
theorem Prepared.centered_isotropic_at
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared .centered M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hl : leakage ω N I ≤ leakageBudget params η h) (hN : w * n / 4 ≤ N.card)
    (F : Robust.FrameResult d)
    (hF : Robust.CloseFrame (ABBKS26.RefineAux.roundedReference M ω r N I hI) F
      (((params h).w / 2 : ℚ) : ℝ) (|(params h).R| : ℚ)
        (((params h).isotropy / 10000 : ℚ) : ℝ)) :
    (ABBKS26.RefineAux.affineReference
      (ABBKS26.RefineAux.roundedReference M ω r N I hI)
      (F.transform.map (algebraMap ℚ ℝ)) 0).model.Isotropic (params h).isotropy := by
  let p := params h
  let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
  let T := F.transform.map (algebraMap ℚ ℝ)
  let A := ABBKS26.RefineAux.affineReference R T 0
  have hv := hp.reference_valid_at .centered M ε w η Δ D ω r params N I hI
  have hr := hp.reference_resilient_at .centered M ε w η Δ D ω r params N I hI 4
    (by omega) ((by omega : 4 ≤ 8).trans
      (hp.eight_le_degree .centered M ε w η Δ D ω r params)) (by decide)
  have he := hp.close_frame_error_at .centered M ε w η Δ D ω r params h hh
    N I hI hl hN F hF
  obtain ⟨hT, _⟩ := hp.frame_population_cov_at .centered M ε w η Δ D ω r params h hh
    N I hI hl hN F hF
  have hηc := prepared_eta_contamination .centered M ε w η Δ D ω r params hp h hh
  obtain ⟨_, hcen, _, _, _, _, hη, hη100, _, _, _, _, _, _, hready, _⟩ := hp
  have hstep := hready h hh
  have hγ1 : (p.isotropy : ℝ) ≤ 1 := by
    exact_mod_cast stepReady_isotropy_le_one .centered k _ _ hstep
  obtain ⟨hw, hw2, _, _, _, _, _, _, _, _, _, _, hσ, hreq, hζ, hζle, _⟩ := hstep
  change 0 < p.w at hw
  change p.w ≤ 1 / 2 at hw2
  change p.sigmaSq = 600 / (p.w / 2) ^ 2 + 2 * p.R ^ 2 at hσ
  have hσ1 : (1 : ℝ) ≤ p.sigmaSq := by
    exact_mod_cast ABBKS26.RefineAux.sigmaSq_one_le p hw hw2 hσ
  have hγ : (0 : ℝ) < p.isotropy := by
    have hγQ : 0 < p.isotropy := by linarith only [hζ, hζle]
    exact_mod_cast hγQ
  have hreqγ := hreq.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hbudget : (p.contamination : ℝ) * (10 ^ 10 * p.sigmaSq) ≤
      (p.isotropy : ℝ) ^ 2 := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ 10 * p.sigmaSq)).mp
    exact_mod_cast hreqγ
  have hc0 : (0 : ℝ) ≤ p.contamination := (by positivity : 0 ≤ 8 * η).trans hηc
  have hcσ := mul_le_mul_of_nonneg_left hσ1 hc0
  have hγsq : (p.isotropy : ℝ) ^ 2 ≤ p.isotropy := by nlinarith only [hγ.le, hγ1]
  have herror : 2 * ((p.isotropy : ℝ) / 100) + 20 * (η / 10 ^ 8) ≤ p.isotropy := by
    nlinarith only [hηc, hbudget, hcσ, hγsq, hγ.le]
  have hAv : A.Valid (w / 2) := ABBKS26.RefineAux.affineReference_valid R T 0 _ hv hT
  have hAr : A.Resilient 4 (η / 10 ^ 8) :=
    ABBKS26.RefineAux.affineReference_resilient R T 0 _ _ hT hr
  have hAc : ∀ j, A.model.mean j = 0 := by
    intro j
    change T *ᵥ (M.μ (ABBKS26.RefineAux.component I j) - 0) = 0
    rw [hcen, sub_self, mulVec_zero]
  have hAe : frobSq (A.cov - 1) ≤ ((p.isotropy : ℝ) / 100) ^ 2 := by
    rw [ABBKS26.RefineAux.affineReference_cov R T 0 hv.2.2.2.2.1]
    exact he.trans (pow_le_pow_left₀ (by positivity) (by linarith only [hγ.le]) 2)
  exact ABBKS26.RefineAux.isotropic_mono A.model _ _
    (ABBKS26.RefineAux.centered_isotropic_of_empirical A (w / 2) (η / 10 ^ 8)
      (p.isotropy / 100) hAv hAc ⟨by positivity, by linarith only [hη100]⟩ hAr
      ⟨by positivity, by linarith only [hγ1]⟩ hAe) herror


private theorem prepared_verify_budgets
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1) :
    (params h).contamination ≤ (1 / 2 : ℝ) ∧
      0 ≤ (params h).tail + η ∧
      (params h).contamination + 2 * ((params h).tail + η) ≤ (params h).verifyMass ∧
      leakageBudget params η h + (params h).tail + η ≤ 1 / 2 ∧ ε + η ≤ w / 8 := by
  have hweight := hp.weight_at mode M ε w η Δ D ω r params h (by omega)
  have hbudget := hp.leakageBudget_nonneg mode M ε w η Δ D ω r params h (by omega)
  obtain ⟨_, _, _, hw, _, hε, hη, _, _, _, _, _, _, _, hready, hparams⟩ := hp
  obtain ⟨_, hleak, hcont, _, _, _, hsound⟩ := hparams h (by omega)
  obtain ⟨_, hw2, _, _, hφ, htail0, _, _, _, _, _, htail, _, hreq, _⟩ := hready h hh
  have hreqw : (params h).contamination ≤ (params h).w / 800 :=
    hreq.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hreqv : (params h).contamination ≤ (params h).verifyMass / 64 :=
    hreq.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have htailv : (params h).tail ≤ (params h).verifyMass / 64 :=
    htail.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htailφ : (params h).tail ≤ (params h).straddle / 64 :=
    htail.trans (min_le_left _ _)
  have hwR : w ≤ 1 / 2 := by
    have hh : ((params h).w : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hw2
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
    rwa [hweight] at hh
  have hreqwR : (params h).contamination ≤ w / 800 := by
    rw [← hweight]
    exact_mod_cast hreqw
  have hreqvR : (params h).contamination ≤ (params h).verifyMass / (64 : ℝ) := by
    exact_mod_cast hreqv
  have htailvR : (params h).tail ≤ (params h).verifyMass / (64 : ℝ) := by
    exact_mod_cast htailv
  have htailφR : (params h).tail ≤ (params h).straddle / (64 : ℝ) := by
    exact_mod_cast htailφ
  have hφR : (0 : ℝ) < (params h).straddle := by exact_mod_cast hφ
  have htailR : (0 : ℝ) < (params h).tail := by exact_mod_cast htail0
  have hleak0 : (0 : ℝ) ≤ (params h).leakage := hbudget.trans hleak
  have hεη : 8 * (ε + η) ≤ (params h).contamination * w := by
    apply (div_le_iff₀ hw).mp
    apply le_trans _ hcont
    apply div_le_div_of_nonneg_right _ hw.le
    have hn : (0 : ℝ) ≤ 1 / n := by positivity
    linarith only [hleak0, hn]
  have hreq0 : (0 : ℝ) ≤ (params h).contamination := by
    by_contra hn
    have hh := mul_neg_of_neg_of_pos (lt_of_not_ge hn) hw
    linarith only [hεη, hε, hη, hh]
  have hreq1 : (params h).contamination ≤ (1 : ℝ) := by linarith only [hreqwR, hwR]
  have hηreq : η ≤ (params h).contamination / (16 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hwR hreq0
    linarith only [hh, hεη, hε]
  have hsmall := (hsound hh).2.2.2.2.2.2.1
  refine ⟨by linarith only [hreqwR, hwR], by positivity, ?_, ?_, ?_⟩
  · linarith only [hreqvR, htailvR, hηreq, hreq0]
  · linarith only [hsmall, htailφR, hφR, hη, hε, hwR, hweight]
  · have hh := mul_le_mul_of_nonneg_right hreq1 hw.le
    linarith only [hh, hεη]

/-- Clean component window and wrong-side counts suffice for the scheduled check. -/
theorem Prepared.verify_of_component_counts
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (e : Edge n d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hleak : leakage ω e.parent I ≤ leakageBudget params η h)
    (hsize : w * n / 4 ≤ e.parent.card)
    (hwin : ∀ j ∈ I,
      (((cluster (labels ω) j \ corrupted ω).filter fun l ↦
        e.lower ≤ e.statistic.evalQ (r ((ω l).1, (ω l).2.2)) ∧
          e.statistic.evalQ (r ((ω l).1, (ω l).2.2)) ≤ e.upper).card : ℝ) ≤
            ((params h).tail + η) * (cluster (labels ω) j).card)
    (hleft : ∃ j ∈ I,
      (((cluster (labels ω) j \ corrupted ω) ∩
        e.right (fun l i ↦ r ((ω l).1, (ω l).2.2) i)).card : ℝ) ≤
          ((params h).tail + η) * (cluster (labels ω) j).card)
    (hright : ∃ j ∈ I,
      (((cluster (labels ω) j \ corrupted ω) ∩
        e.left (fun l i ↦ r ((ω l).1, (ω l).2.2) i)).card : ℝ) ≤
          ((params h).tail + η) * (cluster (labels ω) j).card) :
    Verify (params h) (fun l i ↦ r ((ω l).1, (ω l).2.2) i) e := by
  have hcont := hp.contamination_at mode M ε w η Δ D ω r params h (by omega)
    e.parent I hI hleak hsize
  obtain ⟨hhalf, ht, hv, hs, hξ⟩ :=
    prepared_verify_budgets mode M ε w η Δ D ω r params hp h hh
  have hweight := hp.weight_at mode M ε w η Δ D ω r params h (by omega)
  obtain ⟨_, _, _, _, hwj, _, hη, hη100, _, hg, _⟩ := hp
  obtain ⟨hcounts, hbad⟩ := good_counts M ε w η D ω hg ⟨hη.le, hη100⟩
  apply RefineAux.verify_of_component_counts ω _ (params h) e I w
    (leakageBudget params η h) (params h).contamination ((params h).tail + η) (ε + η)
    hweight hleak hcont hhalf ht hv (by simpa only [add_assoc] using hs) hξ _ hbad
    hwin hleft hright
  intro j
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hwj j) (by norm_num))
    (Nat.cast_nonneg _)).trans (hcounts j).1

/-- Buffered population completeness survives corruption, leakage, and rounding. -/
theorem Prepared.verify_of_bufferedComplete
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (e : Edge n d) (I J : Finset (Fin k)) (hI : I.Nonempty)
    (hleak : leakage ω e.parent I ≤ leakageBudget params η h)
    (hsize : w * n / 4 ≤ e.parent.card)
    (hpop : RefineAux.BufferedComplete M I J (params h) η e) :
    Verify (params h) (fun l i ↦ r ((ω l).1, (ω l).2.2) i) e := by
  classical
  have hn := prepared_rounding_bound mode M ε w η Δ D ω r params hp
  have hv := hp.verify_of_component_counts mode M ε w η Δ D ω r params h hh e I
    hI hleak hsize
  obtain ⟨hM, _, _, _, _, _, hη, hη100, _, hg, hr, _⟩ := hp
  obtain ⟨hJI, hJ, hIJ, hpop⟩ := hpop
  apply hv
  · intro j hj
    obtain ⟨C⟩ := SoundAux.exists_coordinates M hM j e.statistic
    have hc := RefineAux.upper_window M ε w η D ω r hM hg hr ⟨hη, hη100⟩ hn j
      e.statistic C e.lower e.upper
    have hbound := hc.trans (mul_le_mul_of_nonneg_right
      (add_le_add (hpop j hj C).1 (le_refl η)) (Nat.cast_nonneg _))
    simpa only [SoundAux.value, Rat.cast_le] using hbound
  · obtain ⟨j, hj⟩ := hJ
    obtain ⟨C⟩ := SoundAux.exists_coordinates M hM j e.statistic
    have hp := (hpop j (hJI hj) C).2
    simp only [hj, ite_true] at hp
    have hc := RefineAux.upper_right M ε w η D ω r hM hg hr ⟨hη, hη100⟩ hn j
      e.statistic C e.threshold
    have hbound := hc.trans (mul_le_mul_of_nonneg_right (add_le_add hp (le_refl η))
      (Nat.cast_nonneg _))
    have hb : (((cluster (labels ω) j \ corrupted ω).filter fun l ↦
        e.threshold < e.statistic.evalQ (r ((ω l).1, (ω l).2.2))).card : ℝ) ≤
          ((params h).tail + η) * (cluster (labels ω) j).card := by
      simpa only [SoundAux.value, Rat.cast_lt] using hbound
    refine ⟨j, hJI hj, le_trans ?_ hb⟩
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro l hl
    obtain ⟨hlc, hlr⟩ := Finset.mem_inter.mp hl
    obtain ⟨hlN, hln⟩ := Finset.mem_sdiff.mp hlr
    refine Finset.mem_filter.mpr ⟨hlc, ?_⟩
    apply lt_of_not_ge
    intro hle
    exact hln (Finset.mem_filter.mpr ⟨hlN, hle⟩)
  · obtain ⟨j, hj⟩ := hIJ
    obtain ⟨hjI, hjJ⟩ := Finset.mem_sdiff.mp hj
    obtain ⟨C⟩ := SoundAux.exists_coordinates M hM j e.statistic
    have hp := (hpop j hjI C).2
    simp only [hjJ, ite_false] at hp
    have hc := RefineAux.upper_left M ε w η D ω r hM hg hr ⟨hη, hη100⟩ hn j
      e.statistic C e.threshold
    have hbound := hc.trans (mul_le_mul_of_nonneg_right (add_le_add hp (le_refl η))
      (Nat.cast_nonneg _))
    have hb : (((cluster (labels ω) j \ corrupted ω).filter fun l ↦
        e.statistic.evalQ (r ((ω l).1, (ω l).2.2)) ≤ e.threshold).card : ℝ) ≤
          ((params h).tail + η) * (cluster (labels ω) j).card := by
      simpa only [SoundAux.value, Rat.cast_le] using hbound
    refine ⟨j, hjI, le_trans ?_ hb⟩
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro l hl
    obtain ⟨hlc, hll⟩ := Finset.mem_inter.mp hl
    exact Finset.mem_filter.mpr ⟨hlc, (Finset.mem_filter.mp hll).2⟩


/-- Verification at a prepared depth gives the exact leakage budget for the next depth. -/
theorem Prepared.split_sound_at
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (e : Edge n d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hl : leakage ω e.parent I ≤ leakageBudget params η h)
    (hs : ScaleValid M I (params h) e)
    (hv : Verify (params h) (fun l i ↦ r ((ω l).1, (ω l).2.2) i) e) :
    ∃ L R : Finset (Fin k), L.Nonempty ∧ R.Nonempty ∧ Disjoint L R ∧ L ∪ R = I ∧
      leakage ω (e.left (fun l i ↦ r ((ω l).1, (ω l).2.2) i)) L ≤
        leakageBudget params η (h + 1) ∧
      leakage ω (e.right (fun l i ↦ r ((ω l).1, (ω l).2.2) i)) R ≤
        leakageBudget params η (h + 1) := by
  have hn := prepared_rounding_bound mode M ε w η Δ D ω r params hp
  obtain ⟨hM, _, _, _, hwj, _, _, _, _, hg, hr, _, _, _, _, hparams⟩ := hp
  obtain ⟨hw, _, _, _, _, _, hcond⟩ := hparams h (by omega)
  have hg' : Good M ε (params h).w η D ω := by rwa [hw]
  have hwj' : ∀ j, ((params h).w : ℝ) ≤ M.w j := by rwa [hw]
  rw [leakageBudget_succ]
  exact split_sound M ε η (leakageBudget params η h) D ω r (params h) e I
    hM hg' hr hI hl hwj' hs (hcond hh) hn hv

/-- A verified, scale-valid edge extends a good partition by one block. -/
theorem Prepared.replace_goodPartition
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (C : Candidate n d)
    (hh : C.path.length < k - 1) (I : Fin C.blocks.length → Finset (Fin k))
    (hS : WeakPartition C.blocks) (hI : ∀ a, (I a).Nonempty)
    (hdis : ∀ a b, a ≠ b → Disjoint (I a) (I b))
    (hcover : Finset.univ.biUnion I = Finset.univ)
    (hbound : ∀ a, leakage ω C.blocks[a] (I a) ≤ leakageBudget params η C.path.length ∧
      w * n / 4 ≤ C.blocks[a].card)
    (j : Fin C.blocks.length) (e : Edge n d) (he : e.parent = C.blocks[j])
    (hs : ScaleValid M (I j) (params C.path.length) e)
    (hv : Verify (params C.path.length) (fun l i ↦ r ((ω l).1, (ω l).2.2) i) e) :
    GoodPartition ω w (leakageBudget params η (C.path.length + 1))
      (replaceBlock (fun l i ↦ r ((ω l).1, (ω l).2.2) i) C j e).blocks := by
  have hl : leakage ω e.parent (I j) ≤ leakageBudget params η C.path.length := by
    rw [he]
    exact (hbound j).1
  obtain ⟨L, R, hL, hR, hLR, hu, hl, hr⟩ :=
    hp.split_sound_at mode M ε w η Δ D ω r params C.path.length hh e (I j) (hI j) hl hs hv
  have hw := hp.weight_at mode M ε w η Δ D ω r params C.path.length (by omega)
  have hA : w * n / 4 ≤ (e.left (fun l i ↦ r ((ω l).1, (ω l).2.2) i)).card := by
    rw [← hw]
    exact_mod_cast hv.2.1
  have hB : w * n / 4 ≤ (e.right (fun l i ↦ r ((ω l).1, (ω l).2.2) i)).card := by
    rw [← hw]
    exact_mod_cast hv.2.2
  apply RefineAux.goodPartition_split ω w _ _ C.blocks I hS hI hdis hcover hbound j
    _ _ L R (split_partition e _).1 ((split_partition e _).2.trans he) hL hR hLR hu
    (hp.leakageBudget_le_succ mode M ε w η Δ D ω r params C.path.length hh) hl hr hA hB

private theorem goodPartition_multicomponent
    (ω : Fin n → Triple k d) (w Φ : ℝ) (S : List (Finset (Fin n)))
    (hS : GoodPartition ω w Φ S) (hlen : S.length < k) :
    ∃ I : Fin S.length → Finset (Fin k),
      (∀ a, (I a).Nonempty) ∧ (∀ a b, a ≠ b → Disjoint (I a) (I b)) ∧
      Finset.univ.biUnion I = Finset.univ ∧
      (∀ a, leakage ω S[a] (I a) ≤ Φ ∧ w * n / 4 ≤ S[a].card) ∧
      ∃ a, 2 ≤ (I a).card := by
  classical
  obtain ⟨_, I, hI, hdis, hcover, hbound⟩ := hS
  refine ⟨I, hI, hdis, hcover, hbound, ?_⟩
  by_contra h
  have hsmall (a : Fin S.length) : (I a).card ≤ 1 := by
    have ha : ¬ 2 ≤ (I a).card := fun ha ↦ h ⟨a, ha⟩
    omega
  have hcard : k ≤ ∑ a : Fin S.length, (I a).card := by
    have hh := Finset.card_biUnion_le (s := Finset.univ) (t := I)
    simpa only [hcover, Finset.card_univ, Fintype.card_fin] using hh
  have hsum : (∑ a : Fin S.length, (I a).card) ≤ S.length := by
    calc ∑ a : Fin S.length, (I a).card ≤ ∑ _a : Fin S.length, 1 :=
        Finset.sum_le_sum fun a _ ↦ hsmall a
      _ = S.length := by simp
  omega


abbrev Refiner := {n d : ℕ} → Mode → ℕ → (ℕ → StepParams) →
  (Fin n → Fin d → ℚ) → ℕ → Candidate n d → List (Candidate n d)

def RefineSpec (ref : Refiner) : Prop :=
  ∀ {n d} mode k params (x : Fin n → Fin d → ℚ) fuel C,
    (ref mode k params x fuel C).length ≤ branchCap mode k params ∧
    (∀ C' ∈ ref mode k params x fuel C, ∃ j : Fin C.blocks.length, ∃ e : Edge n d,
      e.parent = C.blocks[j] ∧ e.depth = C.path.length ∧ C' = replaceBlock x C j e) ∧
    ∀ (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d) r,
      x = (fun l i ↦ r ((ω l).1, (ω l).2.2) i) →
      Prepared mode M ε w η Δ D ω r params →
      localBudget mode k n d params ≤ fuel → C.blocks.length < k →
      C.path.length + 1 = C.blocks.length →
      GoodPartition ω w (leakageBudget params η C.path.length) C.blocks →
      (∀ C' ∈ ref mode k params x fuel C,
        ∀ e ∈ C'.path, e ∉ C.path →
          ∃ I, I.Nonempty ∧ leakage ω e.parent I ≤ leakageBudget params η C.path.length ∧
            ScaleValid M I (params e.depth) e) ∧
      ∃ C' ∈ ref mode k params x fuel C,
        GoodPartition ω w (leakageBudget params η (C.path.length + 1)) C'.blocks ∧
          ∀ e ∈ C'.path, e ∉ C.path → Verify (params e.depth) x e

/-- The only construction-stage verification and merging occurs here, inside RB3. -/
def frobSplits (p : StepParams) (k : ℕ) (x : Fin n → Fin d → ℚ)
    (raw : List (Edge n d)) : List (Edge n d) :=
  raw.foldl (fun out e ↦
    if Verify p x e then
      if out.any (fun e' ↦
        (splitDistance e.parent (e.left x) (e'.left x) : ℚ) < p.w * n / 8) then out
      else if out.length < frobCap k then out ++ [e] else out
    else out) []


/-- The internal Frobenius split list obeys its hard cap on every input. -/
theorem frobSplits_bound
    (p : StepParams) (k : ℕ) (x : Fin n → Fin d → ℚ) (raw : List (Edge n d)) :
    (frobSplits p k x raw).length ≤ frobCap k := by
  unfold frobSplits
  apply List.foldlRecOn (motive := fun out : List (Edge n d) ↦ out.length ≤ frobCap k)
    raw _
  · simp
  · intro out hout e _
    split_ifs with hv hd hc
    · exact hout
    · simpa only [List.length_append, List.length_singleton] using Nat.succ_le_of_lt hc
    · exact hout
    · exact hout

/-- Every retained Frobenius split passed its own window check. -/
theorem frobSplits_verified
    (p : StepParams) (k : ℕ) (x : Fin n → Fin d → ℚ) (raw : List (Edge n d)) :
    ∀ e ∈ frobSplits p k x raw, e ∈ raw ∧ Verify p x e := by
  unfold frobSplits
  apply List.foldlRecOn (motive := fun out ↦ ∀ e ∈ out, e ∈ raw ∧ Verify p x e)
  · simp
  · intro out hout e he
    split_ifs with hv hd hc
    · exact hout
    · intro e' he'
      rcases List.mem_append.mp he' with h | h
      · exact hout e' h
      · obtain rfl := List.mem_singleton.mp h
        exact ⟨he, hv⟩
    · exact hout
    · exact hout

/-- Internal merging cannot remove the existence of a verified split. -/
theorem frobSplits_complete
    (p : StepParams) (k : ℕ) (x : Fin n → Fin d → ℚ) (raw : List (Edge n d))
    (he : ∃ e ∈ raw, Verify p x e) : frobSplits p k x raw ≠ [] := by
  let step := fun (out : List (Edge n d)) (e : Edge n d) ↦
    if Verify p x e then
      if out.any (fun e' ↦
        (splitDistance e.parent (e.left x) (e'.left x) : ℚ) < p.w * n / 8) then out
      else if out.length < frobCap k then out ++ [e] else out
    else out
  have hcap : 0 < frobCap k := by unfold frobCap; positivity
  have hstep (out : List (Edge n d)) (e : Edge n d) :
      step out e = [] ↔ out = [] ∧ ¬ Verify p x e := by
    by_cases hout : out = []
    · subst out
      simp [step, hcap]
    · simp only [step]
      split_ifs <;> simp_all
  have hfold (es out : List (Edge n d)) :
      es.foldl step out = [] ↔ out = [] ∧ ∀ e ∈ es, ¬ Verify p x e := by
    induction es generalizing out with
    | nil => simp
    | cons e es ih =>
      simp only [List.foldl_cons, ih, hstep, List.forall_mem_cons, and_assoc]
  intro h
  obtain ⟨e, hem, hv⟩ := he
  exact ((hfold raw []).mp h).2 e hem hv

/-- The remaining analytic interface, before replacing a block in a candidate. -/
abbrev BlockRefiner := {n d : ℕ} → Mode → ℕ → (ℕ → StepParams) →
  (Fin n → Fin d → ℚ) → ℕ → ℕ → Finset (Fin n) → List (Edge n d)

def BlockRefineSpec (run : BlockRefiner) : Prop :=
  ∀ {n d} mode k params (x : Fin n → Fin d → ℚ) fuel h N,
    (run mode k params x fuel h N).length ≤ stepBranchCap mode k (params h) ∧
    (∀ e ∈ run mode k params x fuel h N, e.parent = N ∧ e.depth = h) ∧
    ∀ (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d) r (I : Finset (Fin k)),
      x = (fun l i ↦ r ((ω l).1, (ω l).2.2) i) →
      Prepared mode M ε w η Δ D ω r params →
      localBudget mode k n d params ≤ fuel → h < k - 1 →
      I.Nonempty → leakage ω N I ≤ leakageBudget params η h → w * n / 4 ≤ N.card →
      (∀ e ∈ run mode k params x fuel h N, ScaleValid M I (params h) e) ∧
      (2 ≤ I.card → ∃ e ∈ run mode k params x fuel h N, Verify (params h) x e)


/-- Only nodes with a valid depth and fewer than `k` blocks initiate block calls. -/
def refinerFromBlocks (run : BlockRefiner) : Refiner :=
  fun mode k params x fuel C ↦
    if C.blocks.length < k ∧ C.path.length + 1 = C.blocks.length then
      (List.finRange C.blocks.length).flatMap fun (j : Fin C.blocks.length) ↦
        (run mode k params x fuel C.path.length C.blocks[j]).map (replaceBlock x C j)
    else []

private theorem stepBranchCap_le
    (mode : Mode) (k : ℕ) (params : ℕ → StepParams) (h : ℕ) (hh : h < k - 1) :
    k * stepBranchCap mode k (params h) ≤ branchCap mode k params := by
  have hfold (xs : List ℕ) (a b : ℕ) (hb : b ≤ a ∨ b ∈ xs) :
      b ≤ xs.foldl max a := by
    induction xs generalizing a with
    | nil => simpa using hb
    | cons x xs ih =>
      apply ih
      rcases hb with hb | hb
      · exact Or.inl (hb.trans (le_max_left _ _))
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact Or.inl (le_max_right _ _)
        · exact Or.inr hb
  apply le_trans (Nat.mul_le_mul_left k (hfold _ 0 _ (Or.inr ?_))) (le_max_right 1 _)
  exact List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩

private theorem flatMap_length_le {α β : Type*} (xs : List α) (f : α → List β) (b : ℕ)
    (hb : ∀ a ∈ xs, (f a).length ≤ b) : (xs.flatMap f).length ≤ xs.length * b := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    exact (Nat.add_le_add (hb a (by simp)) (ih (fun a ha ↦ hb a (by simp [ha])))).trans_eq
      (Nat.add_comm _ _)

/-- Once bounded block lists are supplied, all candidate-level obligations follow. -/
theorem refine_spec (run : BlockRefiner) (hrun : BlockRefineSpec run) :
    RefineSpec (refinerFromBlocks run) := by
  classical
  intro n d mode k params x fuel C
  by_cases hguard : C.blocks.length < k ∧ C.path.length + 1 = C.blocks.length
  · have hh : C.path.length < k - 1 := by omega
    have hlen : (refinerFromBlocks run mode k params x fuel C).length ≤
        C.blocks.length * stepBranchCap mode k (params C.path.length) := by
      simp only [refinerFromBlocks, ite_eq_left hguard]
      apply (flatMap_length_le _ _ _ ?_).trans_eq
        (by rw [List.length_finRange])
      intro j _
      simpa only [List.length_map] using (hrun mode k params x fuel C.path.length
        C.blocks[j]).1
    refine ⟨hlen.trans ((Nat.mul_le_mul_right _ (Nat.le_of_lt hguard.1)).trans
      (stepBranchCap_le mode k params C.path.length hh)), ?_, ?_⟩
    · intro C' hC'
      simp only [refinerFromBlocks, ite_eq_left hguard, List.mem_flatMap, List.mem_map] at hC'
      obtain ⟨j, _, e, hem, rfl⟩ := hC'
      obtain ⟨hp, hd⟩ := (hrun mode k params x fuel C.path.length C.blocks[j]).2.1 e hem
      exact ⟨j, e, hp, hd, rfl⟩
    · intro M ε w η Δ D ω r hx hp hf _ _ hgood
      obtain ⟨I, hI, hdis, hcover, hbound, j, hj⟩ :=
        goodPartition_multicomponent ω w _ C.blocks hgood hguard.1
      have hb (a : Fin C.blocks.length) :=
        (hrun mode k params x fuel C.path.length (C.blocks.get a)).2.2
          M ε w η Δ D ω r (I a)
          hx hp hf hh (hI a) (hbound a).1 (hbound a).2
      constructor
      · intro C' hC' e' he' hnew
        simp only [refinerFromBlocks, ite_eq_left hguard, List.mem_flatMap, List.mem_map] at hC'
        obtain ⟨a, _, e, hem, rfl⟩ := hC'
        have he : e' = e := by
          change e' ∈ C.path ++ [e] at he'
          exact List.mem_singleton.mp ((List.mem_append.mp he').resolve_left hnew)
        subst e'
        obtain ⟨hparent, hdepth⟩ :=
          (hrun mode k params x fuel C.path.length (C.blocks.get a)).2.1 e hem
        refine ⟨I a, hI a, ?_, ?_⟩
        · rw [hparent]
          exact (hbound a).1
        · rw [hdepth]
          exact (hb a).1 e hem
      · obtain ⟨e, hem, hv⟩ := (hb j).2 hj
        obtain ⟨hparent, hdepth⟩ :=
          (hrun mode k params x fuel C.path.length (C.blocks.get j)).2.1 e hem
        refine ⟨replaceBlock x C j e, ?_, ?_, ?_⟩
        · simp only [refinerFromBlocks, ite_eq_left hguard, List.mem_flatMap, List.mem_map]
          exact ⟨j, List.mem_finRange j, e, hem, rfl⟩
        · rw [hx]
          apply hp.replace_goodPartition mode M ε w η Δ D ω r params C hh I hgood.1 hI
            hdis hcover hbound j e hparent ((hb j).1 e hem)
          rwa [← hx]
        · intro e' he' hnew
          change e' ∈ C.path ++ [e] at he'
          have he : e' = e :=
            List.mem_singleton.mp ((List.mem_append.mp he').resolve_left hnew)
          subst e'
          rwa [hdepth]
  · refine ⟨?_, ?_, ?_⟩
    · simp [refinerFromBlocks, hguard]
    · simp [refinerFromBlocks, hguard]
    · intro M ε w η Δ D ω r hx hp hf hlt hdepth
      exact (hguard ⟨hlt, hdepth⟩).elim


/-- Every prepared centered node is compatible with the observed-input uniform pool bounds. -/
theorem Prepared.centered_reference_compatible_at
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared .centered M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hl : leakage ω N I ≤ leakageBudget params η h) (hN : w * n / 4 ≤ N.card) :
    ABBKS26.RefineAux.CenteredCompatible
      (fun l i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ)) N
      (((params h).w / 2 : ℚ) : ℝ) (|(params h).R| : ℚ)
      (ABBKS26.RefineAux.roundedReference M ω r N I hI) ∧
      (((params h).w / 2 : ℚ) : ℝ) ≤ 1 := by
  obtain ⟨hv, hres, hπ, _, he⟩ := prepared_loop_hypotheses .centered
    M ε w η Δ D ω r params hp h hh N I hI hl hN
  exact ⟨⟨hv, hres, rfl, rfl, fun j ↦ hp.2.1 _, he.trans (min_le_left _ _)⟩, hπ⟩

end

end ABBKS26.Tree
