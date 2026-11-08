module

public import BB20.LowerBound.Field

/-!
# The lower bound on `ν` (the analogue of [HKM17, Theorem 4.6] used in [BB20, Theorem 5])

If some variable `i ∉ S ∪ {u}` shares with `u` a Fourier coefficient of absolute value at least
`κ > 0`, then some set `I` of at most `d - 1` MRF neighbours of `u` outside `S` has
`ν_{u,I|S} ≥ 2τ(κ)`, with `τ` as in `BB20.tau`.

The proof (helpers in `BB20/LowerBound/`) is a direct argument for `±1` variables. Let `E_u` be
the local field of `u` (`BB20.RBM.field`) and `m_A = E[X_u | X_A]`. The quantity
`C = E[E_u (X_u - m_S)]` is bounded on both sides:

* **From above**, by `2^d γ max_I ν_{u,I|S}`: writing `E_u = ∑_{T' ∋ u} f̂(T') χ_{T' ∖ u}`, the
  term of `T'` has covariance with `X_u` given `X_S` at most `|f̂(T')| 2^{|I|+1} ν_{u,I|S}` with
  `I = T' ∖ (S ∪ {u})` (`BB20.LowerBound.abs_sum_mul_spin_sub_le`), which vanishes for `I = ∅`;
  otherwise `I` is a set of at most `d - 1` neighbours of `u` outside `S`, and
  `∑_{T' ∋ u} |f̂(T')| ≤ γ`.
* **From below**, by `2κ² δ^{D+1} / cosh²(γ)`: since `E[X_u | X_{∖u}] = tanh(E_u)`,
  `C ≥ E[(E_u - E[E_u | X_S])²] / cosh²(γ)` (`BB20.LowerBound.sum_sq_div_cosh_sq_le`), and for
  the `i ∈ T ∖ (S ∪ {u})` some `x₀` has `|E_u(x₀) - E_u(x₀^{⊕i})| ≥ 2κ`, which makes the
  conditional variance at least `2κ² δ^{D+1}` (`BB20.LowerBound.le_sum_sq_sub`).

Comparing the two gives `ν_{u,I|S} ≥ 2κ² δ^{D+1} / (2^d γ cosh²(γ)) > 2τ` for some `I`.
-/

@[expose] public section

namespace BB20.LowerBound

open Finset

/-- **The lower bound on `ν`.** -/
theorem exists_nu_ge {n m : ℕ} (R : RBM n m) (γ : ℝ) (d D : ℕ) (hγ : 0 < γ) (hd : 1 ≤ d)
    (hW : R.WidthLE γ) (hL : R.LatentDegreeLE d) (hDeg : R.DegreeLE D) (u : Fin n)
    (S : Finset (Fin n)) (huS : u ∉ S) (κ : ℝ) (hκ : 0 < κ) (T : Finset (Fin n)) (huT : u ∈ T)
    (hTS : ¬ T ⊆ insert u S) (hT : κ ≤ |R.fourier T|) :
    ∃ I ⊆ R.nbhd u \ S, I.Nonempty ∧ I.card ≤ d - 1 ∧ 2 * tau κ γ d D ≤ R.nu u I S := by
  -- The variable `i ∈ T ∖ (S ∪ {u})`, a neighbour of `u`; `2 ≤ |T| ≤ d`.
  have hT0 : R.fourier T ≠ 0 := fun h ↦ by
    rw [h, abs_zero] at hT
    linarith
  obtain ⟨i, hiT, hiuS⟩ := not_subset.mp hTS
  have hiu : i ≠ u := fun h ↦ hiuS (h ▸ mem_insert_self u S)
  have hiS : i ∉ S := fun h ↦ hiuS (mem_insert_of_mem h)
  have hT2 : 2 ≤ T.card := by
    have hsub : ({u, i} : Finset (Fin n)) ⊆ T := by
      intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · exact huT
      · rw [mem_singleton.mp hj]
        exact hiT
    simpa [card_pair hiu.symm] using card_le_card hsub
  have hd2 : 2 ≤ d := hT2.trans (R.card_le_of_fourier_ne_zero hL T hT2 hT0)
  have hiN : i ∈ R.nbhd u := by
    simp only [RBM.nbhd, mem_filter, mem_univ, true_and]
    exact ⟨hiu, T, huT, hiT, hT0⟩
  -- The lower bound on `C = E[E_u (X_u - E[X_u | X_S])]`.
  obtain ⟨x₀, hx₀⟩ := exists_abs_field_sub_ge R u i huT hiT hiu
  have hC_lower : 2 * κ ^ 2 * condLB γ ^ (D + 1) / Real.cosh γ ^ 2 ≤
      ∑ x, R.obsProb x * R.field u x * (spin (x u) - condE R S (fun y ↦ spin (y u)) x) := by
    have hvar := le_sum_sq_sub R hW hDeg u i hiN hκ.le x₀ (by linarith) (condE R S (R.field u))
      fun x ↦ condE_congr R _ fun j hj ↦ flipAt_of_ne (by rintro rfl; exact hiS hj) x
    exact (div_le_div_of_nonneg_right hvar (by positivity)).trans
      (sum_sq_div_cosh_sq_le R hW u S huS)
  -- The upper bound on `C`, if every candidate `I` had `ν_{u,I|S} < 2τ`.
  by_contra hcon
  push Not at hcon
  have hτ : 0 ≤ 2 * tau κ γ d D := by
    unfold tau
    have := condLB_pos γ
    positivity
  have hterm : ∀ T' ∈ univ.filter (u ∈ ·), R.fourier T' * ∑ x, R.obsProb x *
      chi (T'.erase u) x * (spin (x u) - condE R S (fun y ↦ spin (y u)) x) ≤
      |R.fourier T'| * (2 ^ d * (2 * tau κ γ d D)) := by
    intro T' hT'
    have huT' : u ∈ T' := (mem_filter.mp hT').2
    have hIS : Disjoint (T'.erase u \ S) S := disjoint_sdiff_self_left
    have hdep : ∀ x y : Config n, (∀ j ∈ (T'.erase u \ S) ∪ S, x j = y j) →
        chi (T'.erase u) x = chi (T'.erase u) y := by
      intro x y h
      refine chi_congr fun j hj ↦ h j ?_
      by_cases hjS : j ∈ S
      · exact mem_union_right _ hjS
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hj, hjS⟩)
    have hF := abs_sum_mul_spin_sub_le R u (T'.erase u \ S) S hIS (chi (T'.erase u))
      (fun x ↦ (abs_chi _ _).le) hdep
    by_cases h0 : R.fourier T' = 0
    · simp [h0]
    by_cases hI : (T'.erase u \ S).Nonempty
    · have hsub : T'.erase u \ S ⊆ R.nbhd u \ S := by
        intro j hj
        obtain ⟨hj1, hjS⟩ := mem_sdiff.mp hj
        obtain ⟨hju, hjT'⟩ := mem_erase.mp hj1
        refine mem_sdiff.mpr ⟨?_, hjS⟩
        simp only [RBM.nbhd, mem_filter, mem_univ, true_and]
        exact ⟨hju, T', huT', hjT', h0⟩
      have hT'2 : 2 ≤ T'.card := by
        obtain ⟨j, hj⟩ := hI
        obtain ⟨hju, hjT'⟩ := mem_erase.mp (mem_sdiff.mp hj).1
        have hsub' : ({u, j} : Finset (Fin n)) ⊆ T' := by
          intro k hk
          rcases mem_insert.mp hk with rfl | hk
          · exact huT'
          · rw [mem_singleton.mp hk]
            exact hjT'
        simpa [card_pair hju.symm] using card_le_card hsub'
      have hT'd := R.card_le_of_fourier_ne_zero hL T' hT'2 h0
      have hIcard : (T'.erase u \ S).card ≤ d - 1 :=
        (card_le_card sdiff_subset).trans (by rw [card_erase_of_mem huT']; omega)
      have hν := hcon _ hsub hI hIcard
      have hνnn := R.nu_nonneg u (T'.erase u \ S) S
      have hpow : (2 : ℝ) ^ ((T'.erase u \ S).card + 1) ≤ 2 ^ d :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      calc R.fourier T' * ∑ x, R.obsProb x * chi (T'.erase u) x *
            (spin (x u) - condE R S (fun y ↦ spin (y u)) x)
          ≤ |R.fourier T'| * |∑ x, R.obsProb x * chi (T'.erase u) x *
            (spin (x u) - condE R S (fun y ↦ spin (y u)) x)| := by
            rw [← abs_mul]
            exact le_abs_self _
        _ ≤ |R.fourier T'| * (2 ^ ((T'.erase u \ S).card + 1) * R.nu u (T'.erase u \ S) S) :=
            mul_le_mul_of_nonneg_left hF (abs_nonneg _)
        _ ≤ |R.fourier T'| * (2 ^ d * (2 * tau κ γ d D)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hpow hν.le hνnn (by positivity))
              (abs_nonneg _)
    · rw [not_nonempty_iff_eq_empty] at hI
      have hzero := sum_mul_sub_condE R S (chi (T'.erase u)) (fun y ↦ spin (y u))
        fun x y h ↦ hdep x y (by rwa [hI, empty_union])
      rw [hzero, mul_zero]
      positivity
  have hC_upper : ∑ x, R.obsProb x * R.field u x *
      (spin (x u) - condE R S (fun y ↦ spin (y u)) x) ≤ γ * (2 ^ d * (2 * tau κ γ d D)) := by
    have hdecomp : ∑ x, R.obsProb x * R.field u x *
        (spin (x u) - condE R S (fun y ↦ spin (y u)) x) =
        ∑ T' ∈ univ.filter (u ∈ ·), R.fourier T' * ∑ x, R.obsProb x *
          chi (T'.erase u) x * (spin (x u) - condE R S (fun y ↦ spin (y u)) x) := by
      simp only [RBM.field, mul_sum, sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
    rw [hdecomp]
    calc _ ≤ ∑ T' ∈ univ.filter (u ∈ ·), |R.fourier T'| * (2 ^ d * (2 * tau κ γ d D)) :=
          sum_le_sum hterm
      _ = (∑ T' ∈ univ.filter (u ∈ ·), |R.fourier T'|) * (2 ^ d * (2 * tau κ γ d D)) :=
          (sum_mul _ _ _).symm
      _ ≤ γ * (2 ^ d * (2 * tau κ γ d D)) := mul_le_mul_of_nonneg_right (hW u) (by positivity)
  -- The two bounds contradict each other.
  have hδ := condLB_pos γ
  have hδ1 : condLB γ ≤ 1 := (condLB_le_half hγ.le).trans (by norm_num)
  have hB : (1 : ℝ) ≤ max 1 ((D.choose (d - 1) : ℕ) : ℝ) := le_max_left _ _
  have hdd : (1 : ℝ) ≤ (d : ℝ) ^ (4 * d) := one_le_pow₀ (by exact_mod_cast hd)
  have hpow : condLB γ ^ (d + D - 1) ≤ condLB γ ^ (D + 1) :=
    pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have hE := Real.exp_pos (2 * γ)
  have hcosh : Real.cosh γ ^ 2 ≤ Real.exp (2 * γ) := by
    have h1 : Real.cosh γ ≤ Real.exp γ := by
      rw [Real.cosh_eq]
      linarith [Real.exp_le_exp.mpr (by linarith : -γ ≤ γ)]
    calc Real.cosh γ ^ 2 ≤ Real.exp γ ^ 2 := pow_le_pow_left₀ (Real.cosh_pos γ).le h1 2
      _ = Real.exp (2 * γ) := by
        rw [sq, ← Real.exp_add]
        ring_nf
  have hc := Real.cosh_pos γ
  have h2τ : γ * (2 ^ d * (2 * tau κ γ d D)) = κ ^ 2 * condLB γ ^ (d + D - 1) /
      (2 * ((d : ℝ) ^ (4 * d) * max 1 ((D.choose (d - 1) : ℕ) : ℝ) * Real.exp (2 * γ))) := by
    unfold tau
    rw [pow_succ 2 d]
    field_simp
  have hκ2 : 0 < κ ^ 2 * condLB γ ^ (D + 1) := by positivity
  have key1 : κ ^ 2 * condLB γ ^ (d + D - 1) /
      (2 * ((d : ℝ) ^ (4 * d) * max 1 ((D.choose (d - 1) : ℕ) : ℝ) * Real.exp (2 * γ))) ≤
      κ ^ 2 * condLB γ ^ (D + 1) / (2 * Real.exp (2 * γ)) := by
    apply div_le_div₀ hκ2.le (mul_le_mul_of_nonneg_left hpow (sq_nonneg κ)) (by positivity)
    have : (1 : ℝ) ≤ (d : ℝ) ^ (4 * d) * max 1 ((D.choose (d - 1) : ℕ) : ℝ) := by nlinarith
    nlinarith
  have key2 : κ ^ 2 * condLB γ ^ (D + 1) / (2 * Real.exp (2 * γ)) <
      2 * κ ^ 2 * condLB γ ^ (D + 1) / Real.cosh γ ^ 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end BB20.LowerBound
