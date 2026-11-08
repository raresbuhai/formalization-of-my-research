module

public import BB20.Learning.Progress
public import BB20.Structural
public import BB20.LowerBound

/-!
# The thresholds, and a candidate with a large proxy

* Positivity and scaling of `τ` and `τ'` (`BB20.tau`, `BB20.tauPrime`), and of `η`
  (`BB20.eta`).
* `BB20.Learning.exists_cand`: if some variable `i ∉ S ∪ {u}` shares with `u` a Fourier
  coefficient of absolute value at least `κ > 0`, then some nonempty set `I` of at most `2^s`
  neighbours of `u` outside `S` has `ν_{u,I|S} ≥ 2τ'(κ)`: the lower bound on `ν`
  (`BB20.LowerBound.exists_nu_ge`) followed by Theorem 4 (`BB20.Structural.nuSubsetBound`).
-/

@[expose] public section

namespace BB20.Learning

open Finset

/-- The factor `(4c)^{2^s} c^{2^s (2^s + 1)}` of Theorem 4. -/
noncomputable def thmFactor (s : ℕ) (c : ℝ) : ℝ := (4 * c) ^ 2 ^ s * c ^ (2 ^ s * (2 ^ s + 1))

theorem thmFactor_mono (s : ℕ) {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) :
    thmFactor s c ≤ thmFactor s d := by
  unfold thmFactor
  have hd : 0 ≤ d := hc.trans hcd
  gcongr

theorem one_le_thmFactor (s : ℕ) {c : ℝ} (hc : 1 ≤ c) : 1 ≤ thmFactor s c := by
  unfold thmFactor
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ hc)

theorem tauPrime_eq (α γ : ℝ) (d D s : ℕ) :
    tauPrime α γ d D s = tau α γ d D / thmFactor s d := rfl

theorem tau_pos {α γ : ℝ} {d D : ℕ} (hα : α ≠ 0) (hγ : 0 < γ) (hd : 1 ≤ d) :
    0 < tau α γ d D := by
  unfold tau
  have hδ := condLB_pos γ
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hmax : (0 : ℝ) < max 1 ((D.choose (d - 1) : ℕ) : ℝ) := lt_max_of_lt_left one_pos
  have hα2 : 0 < α ^ 2 := by positivity
  positivity

theorem tauPrime_pos {α γ : ℝ} {d D s : ℕ} (hα : α ≠ 0) (hγ : 0 < γ) (hd : 1 ≤ d) :
    0 < tauPrime α γ d D s := by
  rw [tauPrime_eq]
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_pos (tau_pos hα hγ hd) (lt_of_lt_of_le one_pos (one_le_thmFactor s hd'))

theorem tauPrime_le_tau {α γ : ℝ} {d D s : ℕ} (hα : α ≠ 0) (hγ : 0 < γ) (hd : 1 ≤ d) :
    tauPrime α γ d D s ≤ tau α γ d D := by
  rw [tauPrime_eq]
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_le_self (tau_pos hα hγ hd).le (one_le_thmFactor s hd')

theorem tauPrime_mul (α η γ : ℝ) (d D s : ℕ) :
    tauPrime (α * η) γ d D s = η ^ 2 * tauPrime α γ d D s := by
  simp only [tauPrime, tau]
  ring

theorem eta_sq (γ : ℝ) (D s : ℕ) :
    eta γ D s ^ 2 =
      condLB γ ^ D / (6 * 2 ^ (D + 2 ^ (s + 1)) * (D : ℝ) ^ (2 ^ s * (2 ^ s + 2))) := by
  unfold eta
  rw [Real.sq_sqrt]
  have := condLB_pos γ
  positivity

theorem eta_pos (γ : ℝ) {D : ℕ} (hD : 1 ≤ D) (s : ℕ) : 0 < eta γ D s := by
  unfold eta
  have := condLB_pos γ
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  positivity

theorem eta_sq_le {γ : ℝ} (hγ : 0 ≤ γ) {D : ℕ} (hD : 1 ≤ D) (s : ℕ) :
    eta γ D s ^ 2 ≤ 1 / 6 := by
  rw [eta_sq]
  have hδ := condLB_pos γ
  have hδ1 : condLB γ ≤ 1 := (condLB_le_half hγ).trans (by norm_num)
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h1 : condLB γ ^ D ≤ 1 := pow_le_one₀ hδ.le hδ1
  have h2 : (1 : ℝ) ≤ 2 ^ (D + 2 ^ (s + 1)) := one_le_pow₀ (by norm_num)
  have h3 : (1 : ℝ) ≤ (D : ℝ) ^ (2 ^ s * (2 ^ s + 2)) := one_le_pow₀ hD'
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_le_mul h2 h3 zero_le_one (by positivity)]

theorem eta_le_one {γ : ℝ} (hγ : 0 ≤ γ) {D : ℕ} (hD : 1 ≤ D) (s : ℕ) : eta γ D s ≤ 1 := by
  have h := eta_sq_le hγ hD s
  have h0 := (eta_pos γ hD s).le
  nlinarith

/-- `(4D)^{2^s} D^{2^s (2^s + 1)} η² = δ^D / (6 · 2^D)`. -/
theorem thmFactor_mul_eta_sq (γ : ℝ) {D : ℕ} (hD : 1 ≤ D) (s : ℕ) :
    thmFactor s D * eta γ D s ^ 2 = condLB γ ^ D / (6 * 2 ^ D) := by
  rw [eta_sq, thmFactor]
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have e1 : (4 * (D : ℝ)) ^ 2 ^ s = 2 ^ 2 ^ (s + 1) * (D : ℝ) ^ 2 ^ s := by
    have : (4 : ℝ) ^ 2 ^ s = (2 ^ 2 ^ s) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [mul_pow, pow_succ, pow_mul, this]
  have e2 : (D : ℝ) ^ 2 ^ s * (D : ℝ) ^ (2 ^ s * (2 ^ s + 1)) =
      (D : ℝ) ^ (2 ^ s * (2 ^ s + 2)) := by
    rw [← pow_add]
    congr 1
    ring
  rw [e1, pow_add]
  have : (0 : ℝ) < (D : ℝ) ^ (2 ^ s * (2 ^ s + 2)) := by positivity
  rw [← e2]
  field_simp
  rw [pow_add]
  ring

/-- **A candidate with a large proxy**: if some variable outside `S ∪ {u}` shares with `u` a
Fourier coefficient of absolute value at least `κ > 0`, then some nonempty set `I` of at most
`2^s` neighbours of `u` outside `S` has `ν_{u,I|S} ≥ 2τ'(κ)`. -/
theorem exists_cand {n m : ℕ} (R : RBM n m) {γ : ℝ} {d D s : ℕ} (hγ : 0 < γ) (hd : 1 ≤ d)
    (hW : R.WidthLE γ) (hL : R.LatentDegreeLE d) (hDeg : R.DegreeLE D) (hs : R.SparsityLE s)
    {u : Fin n} {S : Finset (Fin n)} (huS : u ∉ S) {κ : ℝ} (hκ : 0 < κ) {T : Finset (Fin n)}
    (huT : u ∈ T) (hTS : ¬ T ⊆ insert u S) (hT : κ ≤ |R.fourier T|) :
    ∃ I ⊆ R.nbhd u \ S, I.Nonempty ∧ I.card ≤ 2 ^ s ∧ 2 * tauPrime κ γ d D s ≤ R.nu u I S := by
  obtain ⟨I, hI, hne, hcard, hν⟩ :=
    LowerBound.exists_nu_ge R γ d D hγ hd hW hL hDeg u S huS κ hκ T huT hTS hT
  have hIN : I ⊆ R.nbhd u := hI.trans sdiff_subset
  have hIS : Disjoint I S := disjoint_of_subset_left hI sdiff_disjoint
  obtain ⟨I', hI'I, hcard', hν'⟩ := Structural.nuSubsetBound R s hs u I S hIN huS hIS
  have hc1 : (1 : ℝ) ≤ I.card := by exact_mod_cast hne.card_pos
  have hcd : (I.card : ℝ) ≤ d := by exact_mod_cast hcard.trans (Nat.sub_le d 1)
  have hF : thmFactor s I.card ≤ thmFactor s d := thmFactor_mono s (by linarith) hcd
  have hFpos : 0 < thmFactor s I.card := lt_of_lt_of_le one_pos (one_le_thmFactor s hc1)
  have hτ := tauPrime_pos (D := D) (s := s) hκ.ne' hγ hd
  have hge : 2 * tauPrime κ γ d D s ≤ R.nu u I' S := by
    calc 2 * tauPrime κ γ d D s = 2 * tau κ γ d D / thmFactor s d := by
          rw [tauPrime_eq]
          ring
      _ ≤ R.nu u I S / thmFactor s d := by
          have := hFpos.trans_le hF
          gcongr
      _ ≤ R.nu u I S / thmFactor s I.card :=
          div_le_div_of_nonneg_left (R.nu_nonneg u I S) hFpos hF
      _ ≤ R.nu u I' S := hν'
  refine ⟨I', hI'I.trans hI, ?_, hcard', hge⟩
  rcases I'.eq_empty_or_nonempty with h | h
  · rw [h, nu_empty] at hge
    linarith
  · exact h

end BB20.Learning
