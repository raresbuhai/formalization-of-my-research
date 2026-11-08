module

public import BB20.Model
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Rademacher sums: contraction and the linear class

Exponential moments of suprema of Rademacher sums `∑ₖ εₖ ψₖ(i)` over a finite index set, with
uniform random signs `ε ∈ {±1}^M` (`ε : Fin M → Bool`, the sign of `εₖ` being `BB20.spin (ε k)`).
Sums over `ε` are `2^M` times expectations.

* `BB20.Prediction.contraction`: the **Ledoux–Talagrand contraction principle** for the
  exponential: if `|ψₖ(i) - ψₖ(j)| ≤ |qₖ(i) - qₖ(j)|` and `|ψₖ(i)| ≤ |qₖ(i)|`, then
  `E exp(sup_i ∑ₖ εₖ ψₖ(i)) ≤ E exp(sup_i ∑ₖ εₖ qₖ(i))`. One coordinate at a time, it reduces to
  a two-point inequality (`BB20.Prediction.two_point`), which reduces to
  `eᵃ + eᵇ ≤ e^A + e^B` when `a, b ≤ max(A, B)` and `a + b ≤ A + B`
  (`BB20.Prediction.exp_add_exp_le`).
* `BB20.Prediction.sum_exp_rademacher`: `E exp(∑ₖ εₖ aₖ) = ∏ₖ cosh aₖ ≤ exp(∑ₖ aₖ² / 2)`.
* `BB20.Prediction.sum_exp_sup_linear_le`: for scores `t_i = ∑_{j ∈ F} W_{ij} z_j` that are
  linear in features `|z_j| ≤ 1` with `∑_j |W_{ij}| ≤ B`, the supremum is at most `B` times the
  largest `|∑ₖ εₖ z_j(Xₖ)|` (**Massart's finite-class lemma**, in exponential form):
  `E exp(c sup_i ∑ₖ εₖ t_i(Xₖ)) ≤ 2 |F| exp(c² B² M / 2)`.
* `BB20.Prediction.sum_exp_sup_le`: the two combined, for `ψₖ(i)` that are contractions of
  `c t_i(Xₖ)`.
-/

@[expose] public section

namespace BB20.Prediction

open Real Finset

/-- `eᵃ + eᵇ ≤ e^A + e^B` when `a, b ≤ max(A, B)` and `a + b ≤ A + B`. -/
theorem exp_add_exp_le {a b A B : ℝ} (ha : a ≤ max A B) (hb : b ≤ max A B)
    (hab : a + b ≤ A + B) : exp a + exp b ≤ exp A + exp B := by
  wlog hAB : B ≤ A generalizing A B
  · rw [max_comm] at ha hb
    rw [add_comm (exp A)]
    exact this ha hb (by linarith) (le_of_not_ge hAB)
  wlog hba : b ≤ a generalizing a b
  · rw [add_comm (exp a)]
    exact this hb ha (by linarith) (le_of_not_ge hba)
  rw [max_eq_left hAB] at ha hb
  rcases le_or_gt a B with haB | haB
  · have h1 := exp_le_exp.2 haB
    have h2 := exp_le_exp.2 (hba.trans haB)
    have h3 := exp_le_exp.2 hAB
    linarith
  · have h1 : exp b ≤ exp (A + B - a) := exp_le_exp.2 (by linarith)
    have h2 : exp (A + B - a) * exp a = exp A * exp B := by
      rw [← exp_add, ← exp_add]
      ring_nf
    have h3 : 0 ≤ (exp A - exp a) * (exp a - exp B) :=
      mul_nonneg (sub_nonneg.2 (exp_le_exp.2 ha)) (sub_nonneg.2 (exp_le_exp.2 haB.le))
    have ha0 := exp_pos a
    have key : (exp a + exp (A + B - a)) * exp a ≤ (exp A + exp B) * exp a := by nlinarith
    have := le_of_mul_le_mul_right key ha0
    linarith

theorem le_ciSup_of_finite {ι : Type*} [Finite ι] (f : ι → ℝ) (i : ι) : f i ≤ ⨆ i, f i :=
  le_ciSup (Set.finite_range f).bddAbove i

/-- The **two-point inequality** behind the contraction principle: with one sign `ε` uniform on
`{±1}`, replacing `p` by `q` (with `|p_i - p_j| ≤ |q_i - q_j|` and `|p_i| ≤ |q_i|`) does not
decrease `E exp(sup_i (g_i + ε p_i))`. -/
theorem two_point {ι : Type*} [Finite ι] [Nonempty ι] (g p q : ι → ℝ)
    (h1 : ∀ i j, |p i - p j| ≤ |q i - q j|) (h2 : ∀ i, |p i| ≤ |q i|) :
    ∑ b : Bool, exp (⨆ i, (g i + spin b * p i)) ≤
      ∑ b : Bool, exp (⨆ i, (g i + spin b * q i)) := by
  simp only [Fintype.sum_bool, spin, ite_true, Bool.false_eq_true, ite_false, one_mul,
    neg_one_mul, ← sub_eq_add_neg]
  obtain ⟨i0, hi0⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ g i + p i)
  obtain ⟨j0, hj0⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ g i - p i)
  rw [← hi0, ← hj0]
  have hA := le_ciSup_of_finite (fun i ↦ g i + q i)
  have hB := le_ciSup_of_finite (fun i ↦ g i - q i)
  set A := ⨆ i, (g i + q i)
  set B := ⨆ i, (g i - q i)
  apply exp_add_exp_le
  · have := h2 i0
    have := le_abs_self (p i0)
    have := hA i0
    have := hB i0
    rcases abs_cases (q i0) with ⟨h, _⟩ | ⟨h, _⟩
    · exact le_max_of_le_left (by linarith)
    · exact le_max_of_le_right (by linarith)
  · have := h2 j0
    have := neg_abs_le (p j0)
    have := hA j0
    have := hB j0
    rcases abs_cases (q j0) with ⟨h, _⟩ | ⟨h, _⟩
    · exact le_max_of_le_left (by linarith)
    · exact le_max_of_le_right (by linarith)
  · have := h1 i0 j0
    have := le_abs_self (p i0 - p j0)
    have := hA i0
    have := hB i0
    have := hA j0
    have := hB j0
    rcases abs_cases (q i0 - q j0) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith

theorem sum_fin_succ_pi {M : ℕ} (G : (Fin (M + 1) → Bool) → ℝ) :
    ∑ ε, G ε = ∑ b : Bool, ∑ ε : Fin M → Bool, G (Fin.cons b ε) := by
  rw [← (Fin.consEquiv fun _ ↦ Bool).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The **contraction principle** (Ledoux–Talagrand) for the exponential, with an offset `g`. -/
theorem contraction {ι : Type*} [Finite ι] [Nonempty ι] :
    ∀ (M : ℕ) (ψ q : Fin M → ι → ℝ), (∀ k i j, |ψ k i - ψ k j| ≤ |q k i - q k j|) →
      (∀ k i, |ψ k i| ≤ |q k i|) → ∀ g : ι → ℝ,
      ∑ ε : Fin M → Bool, exp (⨆ i, (g i + ∑ k, spin (ε k) * ψ k i)) ≤
        ∑ ε : Fin M → Bool, exp (⨆ i, (g i + ∑ k, spin (ε k) * q k i))
  | 0, ψ, q, _, _, g => by simp
  | M + 1, ψ, q, h1, h2, g => by
    rw [sum_fin_succ_pi, sum_fin_succ_pi]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    calc ∑ b : Bool, ∑ ε : Fin M → Bool,
          exp (⨆ i, (g i + (spin b * ψ 0 i + ∑ k : Fin M, spin (ε k) * ψ k.succ i)))
        = ∑ b : Bool, ∑ ε : Fin M → Bool,
            exp (⨆ i, ((g i + spin b * ψ 0 i) + ∑ k : Fin M, spin (ε k) * ψ k.succ i)) := by
          simp only [add_assoc]
      _ ≤ ∑ b : Bool, ∑ ε : Fin M → Bool,
            exp (⨆ i, ((g i + spin b * ψ 0 i) + ∑ k : Fin M, spin (ε k) * q k.succ i)) :=
          Finset.sum_le_sum fun b _ ↦ contraction M (fun k ↦ ψ k.succ) (fun k ↦ q k.succ)
            (fun k ↦ h1 k.succ) (fun k ↦ h2 k.succ) _
      _ = ∑ ε : Fin M → Bool, ∑ b : Bool,
            exp (⨆ i, ((g i + ∑ k : Fin M, spin (ε k) * q k.succ i) + spin b * ψ 0 i)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ε _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
          congr 1
          exact iSup_congr fun i ↦ by ring
      _ ≤ ∑ ε : Fin M → Bool, ∑ b : Bool,
            exp (⨆ i, ((g i + ∑ k : Fin M, spin (ε k) * q k.succ i) + spin b * q 0 i)) :=
          Finset.sum_le_sum fun ε _ ↦ two_point _ _ _ (h1 0) (h2 0)
      _ = ∑ b : Bool, ∑ ε : Fin M → Bool,
            exp (⨆ i, (g i + (spin b * q 0 i + ∑ k : Fin M, spin (ε k) * q k.succ i))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun ε _ ↦ ?_
          congr 1
          exact iSup_congr fun i ↦ by ring

/-- `E exp(∑ₖ εₖ aₖ) ≤ exp(∑ₖ aₖ² / 2)`, as a sum over the `2^M` sign vectors. -/
theorem sum_exp_rademacher (M : ℕ) (a : Fin M → ℝ) :
    ∑ ε : Fin M → Bool, exp (∑ k, spin (ε k) * a k) ≤ 2 ^ M * exp (∑ k, a k ^ 2 / 2) := by
  have h : ∑ ε : Fin M → Bool, exp (∑ k, spin (ε k) * a k) =
      ∏ k, (exp (a k) + exp (-a k)) := by
    simp_rw [exp_sum]
    rw [← Fintype.prod_sum (fun k b ↦ exp (spin b * a k))]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    simp [spin]
  rw [h, exp_sum, ← Fin.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun k _ ↦ by positivity) fun k _ ↦ ?_
  have := cosh_le_exp_half_sq (a k)
  rw [cosh_eq] at this
  linarith

/-- **Massart's lemma** in exponential form for the linear class: scores `t_i = ∑_{j ∈ F} W_{ij}
z_j` with `|z_j| ≤ 1` and `∑_j |W_{ij}| ≤ B`. -/
theorem sum_exp_sup_linear_le {Ω ι κ : Type*} [Finite ι] [Nonempty ι] (F : Finset κ)
    (hF : F.Nonempty) (feat : κ → Ω → ℝ) (hfeat : ∀ j ∈ F, ∀ x, |feat j x| ≤ 1)
    (W : ι → κ → ℝ) {B c : ℝ} (hc : 0 ≤ c) (hW : ∀ i, ∑ j ∈ F, |W i j| ≤ B) (M : ℕ)
    (X : Fin M → Ω) :
    ∑ ε : Fin M → Bool, exp (⨆ i, ∑ k, spin (ε k) * (c * ∑ j ∈ F, W i j * feat j (X k))) ≤
      2 * F.card * 2 ^ M * exp (c ^ 2 * B ^ 2 * M / 2) := by
  have hB : 0 ≤ B :=
    le_trans (Finset.sum_nonneg fun j _ ↦ abs_nonneg _) (hW (Classical.arbitrary ι))
  -- the Rademacher sums of the features
  set S : (Fin M → Bool) → κ → ℝ := fun ε j ↦ ∑ k, spin (ε k) * feat j (X k)
  have hpt : ∀ ε : Fin M → Bool, exp (⨆ i, ∑ k, spin (ε k) * (c * ∑ j ∈ F, W i j * feat j (X k)))
      ≤ ∑ j ∈ F, (exp (∑ k, spin (ε k) * (c * B * feat j (X k))) +
        exp (∑ k, spin (ε k) * (-(c * B) * feat j (X k)))) := by
    intro ε
    obtain ⟨j0, hj0, hm⟩ := Finset.exists_mem_eq_sup' hF (fun j ↦ |S ε j|)
    set m := F.sup' hF (fun j ↦ |S ε j|)
    have hsup : (⨆ i, ∑ k, spin (ε k) * (c * ∑ j ∈ F, W i j * feat j (X k))) ≤ c * B * m := by
      refine ciSup_le fun i ↦ ?_
      have hre : ∑ k, spin (ε k) * (c * ∑ j ∈ F, W i j * feat j (X k)) =
          c * ∑ j ∈ F, W i j * S ε j := by
        simp only [S, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
      rw [hre, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hc
      calc ∑ j ∈ F, W i j * S ε j ≤ ∑ j ∈ F, |W i j| * m := by
            refine Finset.sum_le_sum fun j hj ↦ ?_
            calc W i j * S ε j ≤ |W i j * S ε j| := le_abs_self _
              _ = |W i j| * |S ε j| := abs_mul _ _
              _ ≤ |W i j| * m := mul_le_mul_of_nonneg_left
                  (Finset.le_sup' (fun j ↦ |S ε j|) hj) (abs_nonneg _)
        _ = (∑ j ∈ F, |W i j|) * m := by rw [Finset.sum_mul]
        _ ≤ B * m := mul_le_mul_of_nonneg_right (hW i) (by rw [hm]; exact abs_nonneg _)
    calc exp (⨆ i, ∑ k, spin (ε k) * (c * ∑ j ∈ F, W i j * feat j (X k)))
        ≤ exp (c * B * |S ε j0|) := exp_le_exp.2 (hm ▸ hsup)
      _ ≤ exp (∑ k, spin (ε k) * (c * B * feat j0 (X k))) +
            exp (∑ k, spin (ε k) * (-(c * B) * feat j0 (X k))) := by
          have e1 : ∑ k, spin (ε k) * (c * B * feat j0 (X k)) = c * B * S ε j0 := by
            simp only [S, Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ ↦ by ring
          have e2 : ∑ k, spin (ε k) * (-(c * B) * feat j0 (X k)) = -(c * B * S ε j0) := by
            simp only [S, Finset.mul_sum, ← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun k _ ↦ by ring
          rw [e1, e2]
          rcases abs_cases (S ε j0) with ⟨h, _⟩ | ⟨h, _⟩
          · rw [h]
            linarith [exp_pos (-(c * B * S ε j0))]
          · rw [h, mul_neg]
            linarith [exp_pos (c * B * S ε j0)]
      _ ≤ _ := Finset.single_le_sum
            (f := fun j ↦ exp (∑ k, spin (ε k) * (c * B * feat j (X k))) +
              exp (∑ k, spin (ε k) * (-(c * B) * feat j (X k))))
            (fun j _ ↦ by positivity) hj0
  have hj : ∀ j ∈ F, ∀ d : ℝ, |d| ≤ c * B →
      ∑ ε : Fin M → Bool, exp (∑ k, spin (ε k) * (d * feat j (X k))) ≤
        2 ^ M * exp (c ^ 2 * B ^ 2 * M / 2) := by
    intro j hj d hd
    refine (sum_exp_rademacher M _).trans ?_
    gcongr
    calc ∑ k, (d * feat j (X k)) ^ 2 / 2 ≤ ∑ _k : Fin M, (c * B) ^ 2 / 2 := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          have h1 : |d * feat j (X k)| ≤ c * B := by
            rw [abs_mul]
            calc |d| * |feat j (X k)| ≤ c * B * 1 :=
                  mul_le_mul hd (hfeat j hj _) (abs_nonneg _) (by positivity)
              _ = c * B := mul_one _
          have h2 := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
          linarith
      _ = c ^ 2 * B ^ 2 * M / 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  calc ∑ ε : Fin M → Bool, exp (⨆ i, ∑ k, spin (ε k) * (c * ∑ j ∈ F, W i j * feat j (X k)))
      ≤ ∑ ε : Fin M → Bool, ∑ j ∈ F, (exp (∑ k, spin (ε k) * (c * B * feat j (X k))) +
          exp (∑ k, spin (ε k) * (-(c * B) * feat j (X k)))) := Finset.sum_le_sum fun ε _ ↦ hpt ε
    _ = ∑ j ∈ F, (∑ ε : Fin M → Bool, exp (∑ k, spin (ε k) * (c * B * feat j (X k))) +
          ∑ ε : Fin M → Bool, exp (∑ k, spin (ε k) * (-(c * B) * feat j (X k)))) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_add_distrib
    _ ≤ ∑ _j ∈ F, (2 ^ M * exp (c ^ 2 * B ^ 2 * M / 2) + 2 ^ M * exp (c ^ 2 * B ^ 2 * M / 2)) := by
        refine Finset.sum_le_sum fun j hj' ↦ add_le_add (hj j hj' _ ?_) (hj j hj' _ ?_)
        · rw [abs_of_nonneg (by positivity)]
        · rw [abs_neg, abs_of_nonneg (by positivity)]
    _ = 2 * F.card * 2 ^ M * exp (c ^ 2 * B ^ 2 * M / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- Contraction and Massart combined: for `ψₖ(i)` that are contractions of `c t_i(Xₖ)` (with
`t_i` linear as in `BB20.Prediction.sum_exp_sup_linear_le`),
`E exp(sup_i ∑ₖ εₖ ψₖ(i)) ≤ 2 |F| exp(c² B² M / 2)`. -/
theorem sum_exp_sup_le {Ω ι κ : Type*} [Finite ι] [Nonempty ι] (F : Finset κ)
    (hF : F.Nonempty) (feat : κ → Ω → ℝ) (hfeat : ∀ j ∈ F, ∀ x, |feat j x| ≤ 1)
    (W : ι → κ → ℝ) {B c : ℝ} (hc : 0 ≤ c) (hW : ∀ i, ∑ j ∈ F, |W i j| ≤ B) (M : ℕ)
    (X : Fin M → Ω) (ψ : Fin M → ι → ℝ)
    (h1 : ∀ k i i', |ψ k i - ψ k i'| ≤
      c * |∑ j ∈ F, W i j * feat j (X k) - ∑ j ∈ F, W i' j * feat j (X k)|)
    (h2 : ∀ k i, |ψ k i| ≤ c * |∑ j ∈ F, W i j * feat j (X k)|) :
    ∑ ε : Fin M → Bool, exp (⨆ i, ∑ k, spin (ε k) * ψ k i) ≤
      2 * F.card * 2 ^ M * exp (c ^ 2 * B ^ 2 * M / 2) := by
  have h := contraction M ψ (fun k i ↦ c * ∑ j ∈ F, W i j * feat j (X k))
    (fun k i i' ↦ by rw [← mul_sub, abs_mul, abs_of_nonneg hc]; exact h1 k i i')
    (fun k i ↦ by rw [abs_mul, abs_of_nonneg hc]; exact h2 k i) (fun _ ↦ 0)
  simp only [zero_add] at h
  exact h.trans (sum_exp_sup_linear_le F hF feat hfeat W hc hW M X)

end BB20.Prediction
