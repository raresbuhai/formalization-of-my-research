module

public import BGHKLMM26.Hardness.SparsifyProb
public import BGHKLMM26.Hardness.SparsifyArith

/-!
# Sparsification: completeness and soundness

`BGHKLMM26.Hard.sparsify_yes` and `BGHKLMM26.Hard.sparsify_no` ([BGHKLMM26, Section 6]; the
definitions are in `BGHKLMM26/Hardness/Sparsify.lean`), for `S = n D` samples:

* **completeness**: by Hoeffding, the given cut cuts at least `S (c - 1/D)` samples with
  probability `19/20`, and fewer than `180 n` samples are dropped with probability `19/20`
  (`BGHKLMM26.Hard.frac_drops_ge_le`); so the Max-Cut value is at least `c - 181/D`;
* **soundness** (Lemmas 6.6 and 6.7): a cut far from optimal (`W_f < s - η₀/2`) is handled by
  Hoeffding and a union bound over all `2^n` cuts; a near cut lies at a dyadic level
  `η = 2^j λ ∈ [λ, η₀]` (`BGHKLMM26.Hard.exists_level`) and within `δ(η) n`,
  `δ(η) = min(C₁ √η, 1)`, of some `L ∈ 𝓛`; Bernstein bounds the deviation of
  `Z_f - Z_L` (`BGHKLMM26.Hard.frac_pair_dev_le`), with a union bound over the Hamming ball, the
  levels and `𝓛` (`BGHKLMM26.Hard.frac_pairs_le`), and Hoeffding bounds `Z_L`. On the good event
  every cut cuts at most `S (s + 2λ)` samples (`BGHKLMM26.Hard.empCut_le_of_good`), so the Max-Cut
  value is at most `(s + 2λ) D / (D - 180) ≤ s + 1082 λ`.

Constants: `C₀ = 181` for completeness; `C₀ = 1082`, `A₀ = 224 / (D λ²)` for soundness.
-/

@[expose] public section

namespace BGHKLMM26.Hard

open Finset

section Main

variable {Ω : Type} [Fintype Ω] [Nonempty Ω] {n : ℕ}

/-- The score of a cut on one sample. -/
noncomputable def cutScore (dec : Ω → Fin n × Fin n) (f : Fin n → Bool) (x : Ω) : ℝ :=
  if f (dec x).1 ≠ f (dec x).2 then 1 else 0

omit [Fintype Ω] [Nonempty Ω] in
theorem cutScore_mem (dec : Ω → Fin n × Fin n) (f : Fin n → Bool) (x : Ω) :
    0 ≤ cutScore dec f x ∧ cutScore dec f x ≤ 1 := by
  unfold cutScore
  split_ifs <;> norm_num

omit [Nonempty Ω] in
theorem mean_cutScore (dec : Ω → Fin n × Fin n) (f : Fin n → Bool) :
    mean (cutScore dec f) = lawCut dec f := by
  classical
  unfold cutScore lawCut
  exact mean_indicator _

omit [Fintype Ω] [Nonempty Ω] in
theorem sum_cutScore (dec : Ω → Fin n × Fin n) {S : ℕ} (ω : Fin S → Ω) (f : Fin n → Bool) :
    ∑ i, cutScore dec f (ω i) = empCut dec ω f := by
  classical
  unfold cutScore empCut
  rw [card_filter]
  push_cast
  rfl

/-! ### Soundness -/

omit [Nonempty Ω] in
theorem mean_sub' (X Y : Ω → ℝ) : mean (fun x ↦ X x - Y x) = mean X - mean Y := by
  unfold mean
  rw [Finset.sum_sub_distrib, sub_div]

/-- **One far cut** (Hoeffding). -/
theorem frac_cut_dev_le (dec : Ω → Fin n × Fin n) (g : Fin n → Bool) (S : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    frac (fun ω : Fin S → Ω ↦ (S : ℝ) * (lawCut dec g + t) ≤ empCut dec ω g) ≤
      Real.exp (-2 * S * t ^ 2) := by
  have h := frac_sum_ge_le (cutScore dec g) (cutScore_mem dec g) S ht
  rw [mean_cutScore] at h
  simpa only [sum_cutScore] using h

/-- **One near pair** (Bernstein) [BGHKLMM26, Lemma 6.5]: if `g` and `L` differ on at most `δ n`
vertices, the score `1[g cuts] - 1[L cuts]` has variance at most `3 δ`. -/
theorem frac_pair_dev_le (dec : Ω → Fin n × Fin n)
    (htouch : ∀ a, frac (fun x ↦ (dec x).1 = a ∨ (dec x).2 = a) ≤ 3 / n)
    (L g : Fin n → Bool) {δ : ℝ} (hδ : 0 ≤ δ)
    (hgL : ((univ.filter fun a ↦ L a ≠ g a).card : ℝ) ≤ δ * n) (S : ℕ) {t : ℝ} (ht : 0 < t) :
    frac (fun ω : Fin S → Ω ↦ (S : ℝ) * (lawCut dec g - lawCut dec L + t) ≤
        (empCut dec ω g : ℝ) - empCut dec ω L) ≤
      Real.exp (-(S * t ^ 2) / (4 * (3 * δ) + 4 * 1 * t)) := by
  classical
  have hn : 0 < n := Fin.pos (dec (Classical.arbitrary Ω)).1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨U, hU⟩ : ∃ U : Finset (Fin n), U = univ.filter fun a ↦ L a ≠ g a := ⟨_, rfl⟩
  have hM : ∀ x, |cutScore dec g x - cutScore dec L x| ≤ 1 := by
    intro x
    unfold cutScore
    split_ifs <;> norm_num
  have hsq : ∀ x, (cutScore dec g x - cutScore dec L x) ^ 2 ≤
      if ∃ a ∈ U, (dec x).1 = a ∨ (dec x).2 = a then (1 : ℝ) else 0 := by
    intro x
    split_ifs with h
    · have := hM x
      rw [abs_le] at this
      nlinarith
    · push Not at h
      have h1 : g (dec x).1 = L (dec x).1 := by
        by_contra hc
        exact (h (dec x).1 (by rw [hU]; simp [Ne.symm hc])).1 rfl
      have h2 : g (dec x).2 = L (dec x).2 := by
        by_contra hc
        exact (h (dec x).2 (by rw [hU]; simp [Ne.symm hc])).2 rfl
      unfold cutScore
      rw [h1, h2]
      simp
  have hσ : mean (fun x ↦ (cutScore dec g x - cutScore dec L x) ^ 2) ≤ 3 * δ := by
    refine (mean_mono' hsq).trans ?_
    rw [mean_indicator]
    refine (frac_exists_le U _).trans ?_
    refine (sum_le_sum fun a _ ↦ htouch a).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have : (U.card : ℝ) ≤ δ * n := hU ▸ hgL
    calc (U.card : ℝ) * (3 / n) ≤ δ * n * (3 / n) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 3 * δ := by field_simp
  have h := frac_sum_ge_bernstein (fun x ↦ cutScore dec g x - cutScore dec L x) hM hσ S ht
    (by positivity)
  rw [mean_sub', mean_cutScore, mean_cutScore] at h
  simpa only [Finset.sum_sub_distrib, sum_cutScore] using h

/-- `e^{-x} ≤ 1/x`. -/
theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply one_div_le_one_div_of_le hx
  linarith [Real.add_one_le_exp x]

/-- **The level of a near-optimal cut**: for `s - η₀/2 ≤ W ≤ s + λ/2`, a dyadic level
`η = 2^j λ ≤ η₀` with `s - η ≤ W` and `W + η/2 ≤ s + λ` (the least `j` with `s - 2^j λ ≤ W`). -/
theorem exists_level {lam η₀ s W : ℝ} (hlam : 0 < lam) (hlη₀ : lam ≤ η₀) (hW1 : s - η₀ / 2 ≤ W)
    (hW2 : W ≤ s + lam / 2) :
    ∃ j : ℕ, 2 ^ j * lam ≤ η₀ ∧ s - 2 ^ j * lam ≤ W ∧ W + 2 ^ j * lam / 2 ≤ s + lam := by
  classical
  have hex : ∃ j : ℕ, s - 2 ^ j * lam ≤ W := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (η₀ / (2 * lam)) (one_lt_two : (1 : ℝ) < 2)
    refine ⟨j, ?_⟩
    rw [div_lt_iff₀ (by positivity)] at hj
    linarith
  have hspec := Nat.find_spec hex
  rcases h : Nat.find hex with _ | k
  · rw [h] at hspec
    refine ⟨0, by simpa using hlη₀, hspec, ?_⟩
    simp only [pow_zero, one_mul]
    linarith
  · rw [h] at hspec
    have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
    push Not at hmin
    have h2 : (2 : ℝ) ^ (k + 1) * lam = 2 * (2 ^ k * lam) := by ring
    refine ⟨k + 1, ?_, hspec, ?_⟩
    · rw [h2]; linarith
    · rw [h2]; linarith

/-- The Hamming condition of the structure hypothesis gives the capped radius. -/
theorem ham_le_radius {C₁ η : ℝ} (f L : Fin n → Bool)
    (h : ((univ.filter fun a ↦ f a ≠ L a).card : ℝ) ≤ C₁ * Real.sqrt η * n) :
    ((univ.filter fun a ↦ L a ≠ f a).card : ℝ) ≤ radius C₁ η * n := by
  have hc : (univ.filter fun a ↦ L a ≠ f a) = univ.filter fun a ↦ f a ≠ L a := by
    ext a; simp [ne_comm]
  rw [hc, radius, min_mul_of_nonneg _ _ (Nat.cast_nonneg _), one_mul]
  refine le_min h ?_
  exact_mod_cast (card_le_univ _).trans (by simp)

omit [Nonempty Ω] in
/-- **On the good event every cut is small** [BGHKLMM26, Lemmas 6.6 and 6.7]: a far cut by
Hoeffding, a near cut through its level and the nearby `L ∈ 𝓛`. -/
theorem empCut_le_of_good (dec : Ω → Fin n × Fin n) {S : ℕ} (ω : Fin S → Ω) {C₁ η₀ lam s : ℝ}
    (hlam : 0 < lam) (hlη₀ : lam ≤ η₀) (hlaw : ∀ f, lawCut dec f ≤ s + lam / 2)
    (𝓛 : Finset (Fin n → Bool))
    (hstruct : ∀ (f : Fin n → Bool) (η : ℝ), lam ≤ η → η ≤ η₀ → s - η ≤ lawCut dec f →
      ∃ L ∈ 𝓛, ((univ.filter fun a ↦ f a ≠ L a).card : ℝ) ≤
        C₁ * Real.sqrt η * n)
    (hfar : ∀ g, (empCut dec ω g : ℝ) < S * (lawCut dec g + η₀ / 2))
    (hL : ∀ L ∈ 𝓛, (empCut dec ω L : ℝ) < S * (lawCut dec L + lam))
    (hpair : ∀ L ∈ 𝓛, ∀ j : ℕ, 2 ^ j * lam ≤ η₀ → ∀ g,
      ((univ.filter fun a ↦ L a ≠ g a).card : ℝ) ≤ radius C₁ (2 ^ j * lam) * n →
        (empCut dec ω g : ℝ) - empCut dec ω L < S * (lawCut dec g - lawCut dec L + 2 ^ j * lam / 2))
    (f : Fin n → Bool) : (empCut dec ω f : ℝ) ≤ S * (s + 2 * lam) := by
  have hS : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  by_cases hfa : lawCut dec f < s - η₀ / 2
  · have h1 := hfar f
    have h2 : (S : ℝ) * (lawCut dec f + η₀ / 2) ≤ S * (s + 2 * lam) :=
      mul_le_mul_of_nonneg_left (by linarith) hS
    linarith
  · obtain ⟨j, hj1, hj2, hj3⟩ := exists_level hlam hlη₀ (not_lt.1 hfa) (hlaw f)
    have hj0 : lam ≤ 2 ^ j * lam := le_mul_of_one_le_left hlam.le (one_le_pow₀ (by norm_num))
    obtain ⟨L, hL𝓛, hham⟩ := hstruct f (2 ^ j * lam) hj0 hj1 hj2
    have h1 := hpair L hL𝓛 j hj1 f (ham_le_radius f L hham)
    have h2 := hL L hL𝓛
    have h3 : (S : ℝ) * (lawCut dec f + 2 ^ j * lam / 2 + lam) ≤ S * (s + 2 * lam) :=
      mul_le_mul_of_nonneg_left (by linarith) hS
    nlinarith

/-- **All far cuts** (union bound over the `2^n` cuts). -/
theorem frac_far_le (dec : Ω → Fin n × Fin n) (S : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    frac (fun ω : Fin S → Ω ↦ ∃ g ∈ (univ : Finset (Fin n → Bool)),
      (S : ℝ) * (lawCut dec g + t) ≤ empCut dec ω g) ≤ 2 ^ n * Real.exp (-2 * S * t ^ 2) := by
  refine (frac_exists_le _ _).trans ?_
  refine (sum_le_sum fun g _ ↦ frac_cut_dev_le dec g S ht).trans ?_
  simp

/-- **The cuts of `𝓛`** (union bound). -/
theorem frac_list_le (dec : Ω → Fin n × Fin n) (𝓛 : Finset (Fin n → Bool)) (S : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    frac (fun ω : Fin S → Ω ↦ ∃ L ∈ 𝓛, (S : ℝ) * (lawCut dec L + t) ≤ empCut dec ω L) ≤
      𝓛.card * Real.exp (-2 * S * t ^ 2) := by
  refine (frac_exists_le _ _).trans ?_
  refine (sum_le_sum fun g _ ↦ frac_cut_dev_le dec g S ht).trans ?_
  simp

/-- The Hamming ball of radius `r n` around `L`. -/
noncomputable def hamBall (L : Fin n → Bool) (r : ℝ) : Finset (Fin n → Bool) :=
  univ.filter fun g ↦ ((univ.filter fun a ↦ L a ≠ g a).card : ℝ) ≤ r * n

/-- **The near pairs** (union bound over `L ∈ 𝓛`, the levels `j ∈ J`, and the Hamming balls). -/
theorem frac_pairs_le (dec : Ω → Fin n × Fin n)
    (htouch : ∀ a, frac (fun x ↦ (dec x).1 = a ∨ (dec x).2 = a) ≤ 3 / n)
    (𝓛 : Finset (Fin n → Bool)) (J : Finset ℕ) (r τ : ℕ → ℝ) (hr0 : ∀ j ∈ J, 0 < r j)
    (hr1 : ∀ j ∈ J, r j ≤ 1) (hτ : ∀ j ∈ J, 0 < τ j) (S : ℕ) {c : ℝ}
    (hc : ∀ j ∈ J, Real.exp (r j * n * Real.log (Real.exp 1 / r j)) *
      Real.exp (-(S * τ j ^ 2) / (4 * (3 * r j) + 4 * 1 * τ j)) ≤ Real.exp (-c)) :
    frac (fun ω : Fin S → Ω ↦ ∃ L ∈ 𝓛, ∃ j ∈ J, ∃ g ∈ hamBall L (r j),
      (S : ℝ) * (lawCut dec g - lawCut dec L + τ j) ≤ (empCut dec ω g : ℝ) - empCut dec ω L) ≤
      𝓛.card * (J.card * Real.exp (-c)) := by
  refine (frac_exists_le _ _).trans ?_
  have hL : ∀ L ∈ 𝓛, frac (fun ω : Fin S → Ω ↦ ∃ j ∈ J, ∃ g ∈ hamBall L (r j),
      (S : ℝ) * (lawCut dec g - lawCut dec L + τ j) ≤ (empCut dec ω g : ℝ) - empCut dec ω L) ≤
      J.card * Real.exp (-c) := by
    intro L _
    refine (frac_exists_le _ _).trans ?_
    have hj : ∀ j ∈ J, frac (fun ω : Fin S → Ω ↦ ∃ g ∈ hamBall L (r j),
        (S : ℝ) * (lawCut dec g - lawCut dec L + τ j) ≤ (empCut dec ω g : ℝ) - empCut dec ω L) ≤
        Real.exp (-c) := by
      intro j hjJ
      refine (frac_exists_le _ _).trans ?_
      have hg : ∀ g ∈ hamBall L (r j), frac (fun ω : Fin S → Ω ↦
          (S : ℝ) * (lawCut dec g - lawCut dec L + τ j) ≤ (empCut dec ω g : ℝ) - empCut dec ω L) ≤
          Real.exp (-(S * τ j ^ 2) / (4 * (3 * r j) + 4 * 1 * τ j)) := by
        intro g hg
        simp only [hamBall, mem_filter, mem_univ, true_and] at hg
        exact frac_pair_dev_le dec htouch L g (hr0 j hjJ).le hg S (hτ j hjJ)
      refine (sum_le_sum hg).trans ?_
      rw [sum_const, nsmul_eq_mul]
      refine le_trans ?_ (hc j hjJ)
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact card_hammingBall_le L (hr0 j hjJ) (hr1 j hjJ)
    refine (sum_le_sum hj).trans ?_
    simp
  refine (sum_le_sum hL).trans ?_
  simp

/-- **The exponent at one level**: the Hamming ball times Bernstein's bound is at most
`exp(-n D λ² / 112)`. -/
theorem level_exponent_le {C₁ η₀ : ℝ} (hC₁ : 0 < C₁) (hη₀1 : η₀ < 1) {D : ℕ} (hD : (0 : ℝ) < D)
    (hl1 : 1 ≤ Real.log D) (hl : ellReq C₁ ≤ Real.log D) {η : ℝ} (hlη : lam C₁ D ≤ η)
    (hηη₀ : η ≤ η₀) (n : ℕ) :
    Real.exp (radius C₁ η * n * Real.log (Real.exp 1 / radius C₁ η)) *
      Real.exp (-(((n * D : ℕ) : ℝ) * (η / 2) ^ 2) / (4 * (3 * radius C₁ η) + 4 * 1 * (η / 2))) ≤
      Real.exp (-(n * (D * lam C₁ D ^ 2 / 112))) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := radius_entropy_le hC₁ hη₀1 hD hl1 hl hlη hηη₀
  have h2 := bernstein_exponent_ge hC₁ hη₀1 hD hl1 hlη hηη₀
  obtain ⟨E, hE⟩ : ∃ E, E = D * (η / 2) ^ 2 / (12 * radius C₁ η + 4 * (η / 2)) := ⟨_, rfl⟩
  rw [← hE] at h1 h2
  have h3 : -(((n * D : ℕ) : ℝ) * (η / 2) ^ 2) / (4 * (3 * radius C₁ η) + 4 * 1 * (η / 2)) =
      -(n * E) := by
    rw [hE]
    push_cast
    rw [show 4 * (3 * radius C₁ η) + 4 * 1 * (η / 2) = 12 * radius C₁ η + 4 * (η / 2) by ring]
    ring
  rw [h3]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h4 : radius C₁ η * n * Real.log (Real.exp 1 / radius C₁ η) ≤ n * ((1 / 2) * E) := by
    rw [mul_comm (radius C₁ η) n, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 hn
  have h5 : n * (D * lam C₁ D ^ 2 / 112) ≤ n * ((1 / 2) * E) := by
    apply mul_le_mul_of_nonneg_left _ hn
    linarith
  linarith

/-- The final ratio: `D (s + 2λ) / (D - 180) ≤ s + 1082 λ`. -/
theorem value_ratio_le {n D s l : ℝ} (hn : 0 < n) (hD : 360 ≤ D) (hs1 : s ≤ 1)
    (hl : 0 < l) (hDl : 1 ≤ D * l) :
    n * D * (s + 2 * l) / (n * D - 180 * n) ≤ s + 1082 * l := by
  have hden : 0 < n * D - 180 * n := by nlinarith
  rw [div_le_iff₀ hden]
  have h1 : 180 * s ≤ 180 * (D * l) := by linarith
  have h2 : 194760 * l ≤ 900 * (D * l) := by nlinarith
  have : (s + 1082 * l) * (n * D - 180 * n) - n * D * (s + 2 * l) =
      n * (1080 * (D * l) - 180 * s - 194760 * l) := by ring
  nlinarith

/-- The levels `2^j λ ≤ η₀ < 1` have `j < D`. -/
theorem level_lt {C₁ : ℝ} {D j : ℕ} {η₀ : ℝ} (hD : (0 : ℝ) < D) (hl1 : 1 ≤ Real.log D)
    (hj : (2 : ℝ) ^ j * lam C₁ D ≤ η₀) (hη₀1 : η₀ < 1) : j < D := by
  have h1 := one_div_le_lam (C₁ := C₁) hD hl1
  have h2 : (2 : ℝ) ^ j * (1 / D) < 1 :=
    lt_of_le_of_lt ((mul_le_mul_of_nonneg_left h1 (by positivity)).trans hj) hη₀1
  rw [mul_one_div, div_lt_one hD] at h2
  have h3 : 2 ^ j < D := by exact_mod_cast h2
  exact (Nat.lt_two_pow_self).trans h3

/-- The far term: `2^n e^{-n D η₀² / 2} ≤ e^{-n}`. -/
theorem far_term_le {n D : ℕ} {η₀ : ℝ} (hDη : 4 ≤ D * η₀ ^ 2) :
    2 ^ n * Real.exp (-2 * ((n * D : ℕ) : ℝ) * (η₀ / 2) ^ 2) ≤ Real.exp (-n) := by
  have h2 : (2 : ℝ) ^ n ≤ Real.exp n := by
    rw [← mul_one (n : ℝ), Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp 1]) n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  calc (2 : ℝ) ^ n * Real.exp (-2 * ((n * D : ℕ) : ℝ) * (η₀ / 2) ^ 2) ≤
        Real.exp n * Real.exp (-2 * ((n * D : ℕ) : ℝ) * (η₀ / 2) ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (n + -2 * ((n * D : ℕ) : ℝ) * (η₀ / 2) ^ 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-n) := by
        apply Real.exp_le_exp.2
        push_cast
        have : (n : ℝ) * 4 ≤ n * (D * η₀ ^ 2) := mul_le_mul_of_nonneg_left hDη hn
        nlinarith

/-- **The bad events have probability at most `1/10`.** -/
theorem frac_bad_le {C₁ η₀ : ℝ} (hC₁ : 0 < C₁) (hη₀ : 0 < η₀) (hη₀1 : η₀ < 1) {D : ℕ}
    (hD360 : 360 ≤ D)
    (hl1 : 1 ≤ Real.log D) (hl : ellReq C₁ ≤ Real.log D) (hDη : 4 ≤ D * η₀ ^ 2)
    (hn40 : (40 : ℝ) ≤ n) (hnc : 80 * (D + 1) / (D * lam C₁ D ^ 2 / 112) ≤ n) {Δ : ℕ}
    (hΔ : 10 * D ≤ Δ) (dec : Ω → Fin n × Fin n)
    (htouch : ∀ a, frac (fun x ↦ (dec x).1 = a ∨ (dec x).2 = a) ≤ 3 / n)
    (hmax : ∀ e, frac (fun x ↦ dec x = e) ≤ 1 / (n * D ^ 2)) (𝓛 : Finset (Fin n → Bool))
    (h𝓛 : (𝓛.card : ℝ) ≤ Real.exp (n / (2 / (D * lam C₁ D ^ 2 / 112)))) :
    frac (fun ω : Fin (n * D) → Ω ↦
      ((∃ g ∈ (univ : Finset (Fin n → Bool)),
          ((n * D : ℕ) : ℝ) * (lawCut dec g + η₀ / 2) ≤ empCut dec ω g) ∨
        (∃ L ∈ 𝓛, ((n * D : ℕ) : ℝ) * (lawCut dec L + lam C₁ D) ≤ empCut dec ω L)) ∨
      ((∃ L ∈ 𝓛, ∃ j ∈ (range D).filter (fun j ↦ (2 : ℝ) ^ j * lam C₁ D ≤ η₀),
          ∃ g ∈ hamBall L (radius C₁ (2 ^ j * lam C₁ D)),
          ((n * D : ℕ) : ℝ) * (lawCut dec g - lawCut dec L + 2 ^ j * lam C₁ D / 2) ≤
            (empCut dec ω g : ℝ) - empCut dec ω L) ∨
        (180 * n : ℝ) ≤ drops Δ dec ω)) ≤ 1 / 10 := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hD1 : 1 ≤ D := by omega
  have hlam := lam_pos_of_log (C₁ := C₁) hDpos hl1
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = D * lam C₁ D ^ 2 / 112 := ⟨_, rfl⟩
  rw [← hc] at hnc h𝓛
  have hc0 : 0 < c := by rw [hc]; positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnc' : (0 : ℝ) < n * c := by positivity
  have h𝓛' : (𝓛.card : ℝ) ≤ Real.exp (n * c / 2) := by
    refine h𝓛.trans (le_of_eq ?_)
    congr 1
    field_simp
  -- the four terms
  have P1 : frac (fun ω : Fin (n * D) → Ω ↦ ∃ g ∈ (univ : Finset (Fin n → Bool)),
      ((n * D : ℕ) : ℝ) * (lawCut dec g + η₀ / 2) ≤ empCut dec ω g) ≤ 1 / 40 := by
    refine (frac_far_le dec (n * D) (t := η₀ / 2) (by positivity)).trans ?_
    refine (far_term_le hDη).trans ((exp_neg_le_inv hnpos).trans ?_)
    rw [div_le_div_iff₀ hnpos (by norm_num)]
    linarith
  have P2 : frac (fun ω : Fin (n * D) → Ω ↦ ∃ L ∈ 𝓛,
      ((n * D : ℕ) : ℝ) * (lawCut dec L + lam C₁ D) ≤ empCut dec ω L) ≤
      Real.exp (-(n * c / 2)) := by
    refine (frac_list_le dec 𝓛 (n * D) hlam.le).trans ?_
    refine (mul_le_mul_of_nonneg_right h𝓛' (Real.exp_pos _).le).trans ?_
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    push_cast
    have : n * c ≤ 2 * (n * D * lam C₁ D ^ 2) := by
      rw [hc]
      have : (0 : ℝ) ≤ n * D * lam C₁ D ^ 2 := by positivity
      linarith
    nlinarith
  have P3 : frac (fun ω : Fin (n * D) → Ω ↦ ∃ L ∈ 𝓛,
      ∃ j ∈ (range D).filter (fun j ↦ (2 : ℝ) ^ j * lam C₁ D ≤ η₀),
      ∃ g ∈ hamBall L (radius C₁ (2 ^ j * lam C₁ D)),
      ((n * D : ℕ) : ℝ) * (lawCut dec g - lawCut dec L + 2 ^ j * lam C₁ D / 2) ≤
        (empCut dec ω g : ℝ) - empCut dec ω L) ≤ D * Real.exp (-(n * c / 2)) := by
    have hlev : ∀ j ∈ (range D).filter (fun j ↦ (2 : ℝ) ^ j * lam C₁ D ≤ η₀),
        lam C₁ D ≤ 2 ^ j * lam C₁ D ∧ 2 ^ j * lam C₁ D ≤ η₀ := by
      intro j hj
      simp only [mem_filter, mem_range] at hj
      exact ⟨le_mul_of_one_le_left hlam.le (one_le_pow₀ (by norm_num)), hj.2⟩
    have h := frac_pairs_le dec htouch 𝓛 ((range D).filter (fun j ↦ (2 : ℝ) ^ j * lam C₁ D ≤ η₀))
      (fun j ↦ radius C₁ (2 ^ j * lam C₁ D)) (fun j ↦ 2 ^ j * lam C₁ D / 2)
      (fun j hj ↦ radius_pos hC₁ (lt_of_lt_of_le hlam (hlev j hj).1))
      (fun j _ ↦ radius_le_one _ _) (fun j _ ↦ by positivity) (n * D) (c := n * c)
      (fun j hj ↦ by
        have := level_exponent_le hC₁ hη₀1 hDpos hl1 hl (hlev j hj).1 (hlev j hj).2 n
        rw [← hc] at this
        exact this)
    refine h.trans ?_
    have hJ : (((range D).filter (fun j ↦ (2 : ℝ) ^ j * lam C₁ D ≤ η₀)).card : ℝ) ≤ D := by
      exact_mod_cast (card_filter_le _ _).trans (card_range D).le
    calc (𝓛.card : ℝ) * (((range D).filter (fun j ↦ (2 : ℝ) ^ j * lam C₁ D ≤ η₀)).card *
          Real.exp (-(n * c))) ≤ Real.exp (n * c / 2) * (D * Real.exp (-(n * c))) :=
          mul_le_mul h𝓛' (mul_le_mul_of_nonneg_right hJ (Real.exp_pos _).le)
            (by positivity) (Real.exp_pos _).le
      _ = D * Real.exp (-(n * c / 2)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have P4 := frac_drops_ge_le hD1 hΔ dec htouch hmax
  have hE : Real.exp (-(n * c / 2)) ≤ 2 / (n * c) := by
    refine (exp_neg_le_inv (by positivity)).trans (le_of_eq ?_)
    field_simp
  have hE' : (1 + D) * (2 / (n * c)) ≤ 1 / 40 := by
    rw [div_le_iff₀ hc0] at hnc
    rw [mul_div_assoc', div_le_div_iff₀ hnc' (by norm_num)]
    nlinarith
  refine (frac_or_le _ _).trans ?_
  have h12 := (frac_or_le _ _).trans (add_le_add P1 P2)
  have h34 := (frac_or_le _ _).trans (add_le_add P3 P4)
  have := add_le_add h12 h34
  refine this.trans ?_
  have : Real.exp (-(n * c / 2)) + D * Real.exp (-(n * c / 2)) ≤ 1 / 40 := by
    have := mul_le_mul_of_nonneg_left hE (show (0 : ℝ) ≤ 1 + D by positivity)
    nlinarith
  linarith

end Main

/-- **Completeness of the sparsification** [BGHKLMM26, Lemma 6.2 and Theorem 6.1]. -/
theorem sparsify_yes : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ D : ℕ, 1 ≤ D → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ Δ : ℕ, 10 * D ≤ Δ → ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (dec : Ω → Fin n × Fin n),
      (∀ a, frac (fun ω ↦ (dec ω).1 = a ∨ (dec ω).2 = a) ≤ 3 / n) →
      (∀ e, frac (fun ω ↦ dec ω = e) ≤ 1 / (n * D ^ 2)) →
      ∀ (c : ℝ) (f : Fin n → Bool), c ≤ lawCut dec f →
        9 / 10 ≤ frac fun ω : Fin (n * D) → Ω ↦
          c - C₀ / D ≤ maxCutValue (sampledGraph n Δ dec ω) := by
  refine ⟨181, by norm_num, fun D hD ↦ ⟨3 * D, fun n hn Δ hΔ Ω _ _ dec htouch hmax c f hc ↦ ?_⟩⟩
  have hn0 : 0 < n := Fin.pos (dec (Classical.arbitrary Ω)).1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hS : ((n * D : ℕ) : ℝ) = n * D := by push_cast; ring
  have hSpos : (0 : ℝ) < n * D := by positivity
  -- the bad events
  have hB1 := frac_sum_le_le (cutScore dec f) (cutScore_mem dec f) (n * D)
    (t := 1 / D) (by positivity)
  have hB1' : Real.exp (-2 * ((n * D : ℕ) : ℝ) * (1 / D) ^ 2) ≤ 1 / 20 := by
    rw [hS]
    have h3 : (3 * D : ℝ) ≤ n := by exact_mod_cast hn
    have : -2 * (n * D : ℝ) * (1 / D) ^ 2 = -(2 * n / D) := by field_simp
    rw [this]
    have h6 : (6 : ℝ) ≤ 2 * n / D := by rw [le_div_iff₀ hD0]; linarith
    have := Real.quadratic_le_exp_of_nonneg (x := 2 * n / D) (by positivity)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    nlinarith
  have hB2 := frac_drops_ge_le hD hΔ dec htouch hmax
  have hU := frac_or_le (fun ω : Fin (n * D) → Ω ↦
      ∑ i, cutScore dec f (ω i) ≤ ((n * D : ℕ) : ℝ) * (mean (cutScore dec f) - 1 / D))
    (fun ω ↦ (180 * n : ℝ) ≤ drops Δ dec ω)
  have hgood : ∀ ω : Fin (n * D) → Ω,
      ¬ (∑ i, cutScore dec f (ω i) ≤ ((n * D : ℕ) : ℝ) * (mean (cutScore dec f) - 1 / D) ∨
        (180 * n : ℝ) ≤ drops Δ dec ω) → c - 181 / D ≤ maxCutValue (sampledGraph n Δ dec ω) := by
    intro ω hω
    push Not at hω
    obtain ⟨h1, h2⟩ := hω
    rw [sum_cutScore, mean_cutScore, hS] at h1
    have h3 := empCut_sub_drops_le Δ dec ω f
    rw [hS] at h3
    have h4 : (n * D : ℝ) * (c - 181 / D) ≤ n * D * maxCutValue (sampledGraph n Δ dec ω) := by
      have : (n * D : ℝ) * (c - 181 / D) = n * D * (c - 1 / D) - 180 * n := by
        field_simp
        ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hc (le_of_lt hSpos)
      nlinarith
    exact le_of_mul_le_mul_left h4 hSpos
  calc (9 / 10 : ℝ) ≤ 1 - (1 / 20 + 1 / 20) := by norm_num
    _ ≤ 1 - frac (fun ω : Fin (n * D) → Ω ↦
        ∑ i, cutScore dec f (ω i) ≤ ((n * D : ℕ) : ℝ) * (mean (cutScore dec f) - 1 / D) ∨
          (180 * n : ℝ) ≤ drops Δ dec ω) := by linarith
    _ = frac (fun ω : Fin (n * D) → Ω ↦
        ¬ (∑ i, cutScore dec f (ω i) ≤ ((n * D : ℕ) : ℝ) * (mean (cutScore dec f) - 1 / D) ∨
          (180 * n : ℝ) ≤ drops Δ dec ω)) := (frac_not_eq _).symm
    _ ≤ _ := frac_imp_le hgood

/-- **Soundness of the sparsification** [BGHKLMM26, Lemmas 6.6, 6.7, 6.9, 6.10 and Theorem 6.1],
with the robust inverse at the rate `√η`. -/
theorem sparsify_no {C₁ η₀ : ℝ} (hC₁ : 0 < C₁) (hη₀ : 0 < η₀) (hη₀1 : η₀ < 1) :
    ∃ (C₀ : ℝ) (D₀ : ℕ), 0 < C₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∃ (A₀ : ℝ) (n₀ : ℕ), 0 < A₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ Δ : ℕ, 10 * D ≤ Δ →
      ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (dec : Ω → Fin n × Fin n),
      (∀ a, frac (fun ω ↦ (dec ω).1 = a ∨ (dec ω).2 = a) ≤ 3 / n) →
      (∀ e, frac (fun ω ↦ dec ω = e) ≤ 1 / (n * D ^ 2)) →
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (∀ f, lawCut dec f ≤ s + lam C₁ D / 2) →
      ∀ 𝓛 : Finset (Fin n → Bool), (𝓛.card : ℝ) ≤ Real.exp (n / A₀) →
      (∀ (f : Fin n → Bool) (η : ℝ), lam C₁ D ≤ η → η ≤ η₀ → s - η ≤ lawCut dec f →
        ∃ L ∈ 𝓛, ((univ.filter fun a ↦ f a ≠ L a).card : ℝ) ≤
          C₁ * Real.sqrt η * n) →
      9 / 10 ≤ frac fun ω : Fin (n * D) → Ω ↦
        maxCutValue (sampledGraph n Δ dec ω) ≤ s + C₀ * lam C₁ D := by
  obtain ⟨D₀, hD₀⟩ := exists_D₀ C₁ hη₀
  refine ⟨1082, D₀, by norm_num, fun D hD ↦ ?_⟩
  obtain ⟨h360, hl1, hl, hlη₀, hDη₀⟩ := hD₀ D hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlam := lam_pos_of_log (C₁ := C₁) hDpos hl1
  have hc0 : 0 < D * lam C₁ D ^ 2 / 112 := by positivity
  refine ⟨2 / (D * lam C₁ D ^ 2 / 112), ⌈80 * (D + 1) / (D * lam C₁ D ^ 2 / 112)⌉₊ + 40,
    by positivity, fun n hn Δ hΔ Ω _ _ dec htouch hmax s hs0 hs1 hlaw 𝓛 h𝓛 hstruct ↦ ?_⟩
  have hn40 : (40 : ℝ) ≤ n := by exact_mod_cast (show 40 ≤ n by omega)
  have hnc : 80 * (D + 1) / (D * lam C₁ D ^ 2 / 112) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈80 * (D + 1) / (D * lam C₁ D ^ 2 / 112)⌉₊ ≤ n
      by omega))
  have hnpos : (0 : ℝ) < n := by linarith
  have hbad := frac_bad_le (Ω := Ω) hC₁ hη₀ hη₀1 h360 hl1 hl hDη₀ hn40 hnc hΔ dec htouch hmax 𝓛 h𝓛
  have hgood : ∀ ω : Fin (n * D) → Ω, ¬ (
      ((∃ g ∈ (univ : Finset (Fin n → Bool)),
          ((n * D : ℕ) : ℝ) * (lawCut dec g + η₀ / 2) ≤ empCut dec ω g) ∨
        (∃ L ∈ 𝓛, ((n * D : ℕ) : ℝ) * (lawCut dec L + lam C₁ D) ≤ empCut dec ω L)) ∨
      ((∃ L ∈ 𝓛, ∃ j ∈ (range D).filter (fun j ↦ (2 : ℝ) ^ j * lam C₁ D ≤ η₀),
          ∃ g ∈ hamBall L (radius C₁ (2 ^ j * lam C₁ D)),
          ((n * D : ℕ) : ℝ) * (lawCut dec g - lawCut dec L + 2 ^ j * lam C₁ D / 2) ≤
            (empCut dec ω g : ℝ) - empCut dec ω L) ∨
        (180 * n : ℝ) ≤ drops Δ dec ω)) →
      maxCutValue (sampledGraph n Δ dec ω) ≤ s + 1082 * lam C₁ D := by
    intro ω hω
    simp only [not_or, not_exists, not_and, not_le] at hω
    obtain ⟨⟨hfar, hL⟩, hpair, hdrops⟩ := hω
    have hcut := empCut_le_of_good dec ω hlam hlη₀ hlaw 𝓛 hstruct
      (fun g ↦ hfar g (mem_univ g)) hL
      (fun L hL j hj g hg ↦ hpair L hL j
        (by simp only [mem_filter, mem_range]; exact ⟨level_lt hDpos hl1 hj hη₀1, hj⟩) g
        (by simp only [hamBall, mem_filter, mem_univ, true_and]; exact hg))
    have hS : ((n * D : ℕ) : ℝ) = n * D := by push_cast; ring
    have hD360 : (360 : ℝ) ≤ D := by exact_mod_cast h360
    have hKS : (180 * n : ℝ) < ((n * D : ℕ) : ℝ) := by rw [hS]; nlinarith
    refine (maxCutValue_le_of_empCut Δ dec ω hcut hdrops.le hKS).trans ?_
    rw [hS]
    have hDl : (1 : ℝ) ≤ D * lam C₁ D := by
      rw [lam_eq_mul C₁ D hDpos]
      exact one_le_mul_of_one_le_of_one_le (one_le_lamK C₁) hl1
    exact value_ratio_le hnpos hD360 hs1 hlam hDl
  calc (9 / 10 : ℝ) ≤ 1 - 1 / 10 := by norm_num
    _ ≤ 1 - frac (fun ω : Fin (n * D) → Ω ↦
      ((∃ g ∈ (univ : Finset (Fin n → Bool)),
          ((n * D : ℕ) : ℝ) * (lawCut dec g + η₀ / 2) ≤ empCut dec ω g) ∨
        (∃ L ∈ 𝓛, ((n * D : ℕ) : ℝ) * (lawCut dec L + lam C₁ D) ≤ empCut dec ω L)) ∨
      ((∃ L ∈ 𝓛, ∃ j ∈ (range D).filter (fun j ↦ (2 : ℝ) ^ j * lam C₁ D ≤ η₀),
          ∃ g ∈ hamBall L (radius C₁ (2 ^ j * lam C₁ D)),
          ((n * D : ℕ) : ℝ) * (lawCut dec g - lawCut dec L + 2 ^ j * lam C₁ D / 2) ≤
            (empCut dec ω g : ℝ) - empCut dec ω L) ∨
        (180 * n : ℝ) ≤ drops Δ dec ω)) := by linarith
    _ = _ := (frac_not_eq _).symm
    _ ≤ _ := frac_imp_le hgood

end BGHKLMM26.Hard
