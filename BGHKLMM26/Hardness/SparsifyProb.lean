module

public import BGHKLMM26.Hardness.Concentration
public import BGHKLMM26.Hardness.SparsifyGraph
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Sparsification: few samples are dropped

For `S = n D` independent samples of a law on `[n] × [n]` with each vertex an end with probability
at most `3/n` and each ordered pair of probability at most `1/(n D²)` ([BGHKLMM26, Lemmas 6.9 and
6.10]):

* the expected number of loops is at most `n / D` (`BGHKLMM26.Hard.mean_nLoops_le`), of repeated
  samples at most `2n` (`BGHKLMM26.Hard.mean_nReps_le`, by independence of two coordinates,
  `BGHKLMM26.Hard.frac_coord_collide_le`), and of samples beyond the first `Δ ≥ 10 D` at a vertex
  at most `6` (`BGHKLMM26.Hard.mean_overflow_le`, by the binomial tail and `m! ≥ (m/e)^m`);
* so at most `9 n` samples are dropped in expectation (`BGHKLMM26.Hard.mean_drops_le`), and fewer
  than `180 n` with probability at least `19/20` (`BGHKLMM26.Hard.frac_drops_ge_le`).

Also basic facts on `BGHKLMM26.Hard.frac` and `BGHKLMM26.Hard.mean` (union bounds, independence of
coordinates).
-/

@[expose] public section

namespace BGHKLMM26.Hard

open Finset

/-! ### `frac` and `mean` -/

section Frac

variable {β : Type*} [Fintype β]

theorem frac_eq_card (p : β → Prop) [DecidablePred p] :
    frac p = ((univ.filter p).card : ℝ) / Fintype.card β := by
  unfold frac
  congr 3
  ext b
  simp

theorem frac_imp_le {p q : β → Prop} (h : ∀ b, p b → q b) : frac p ≤ frac q := by
  classical
  unfold frac
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact Nat.cast_le.2 (card_le_card fun b hb ↦ by
    simp only [mem_filter, mem_univ, true_and] at hb ⊢; exact h b hb)

theorem frac_nonneg' (p : β → Prop) : 0 ≤ frac p :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem frac_or_le (p q : β → Prop) : frac (fun b ↦ p b ∨ q b) ≤ frac p + frac q := by
  classical
  rw [frac_eq_card, frac_eq_card, frac_eq_card, ← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have : (univ.filter fun b ↦ p b ∨ q b) ⊆ univ.filter p ∪ univ.filter q := by
    intro b hb
    simp only [mem_filter, mem_univ, true_and, mem_union] at hb ⊢
    exact hb
  exact_mod_cast (card_le_card this).trans (card_union_le _ _)

theorem frac_not_eq [Nonempty β] (p : β → Prop) : frac (fun b ↦ ¬ p b) = 1 - frac p := by
  classical
  rw [frac_eq_card, frac_eq_card]
  have hc : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h := card_filter_add_card_filter_not (s := (univ : Finset β)) p
  rw [card_univ] at h
  have h' : ((univ.filter fun b ↦ ¬ p b).card : ℝ) = Fintype.card β - (univ.filter p).card := by
    rw [← h]; push_cast; ring
  rw [h', sub_div, div_self hc]

theorem frac_exists_le {ι : Type*} (s : Finset ι) (p : ι → β → Prop) :
    frac (fun b ↦ ∃ x ∈ s, p x b) ≤ ∑ x ∈ s, frac (p x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frac]
  | insert a s ha ih =>
    rw [sum_insert ha]
    refine (frac_imp_le (q := fun b ↦ p a b ∨ ∃ x ∈ s, p x b) ?_).trans
      ((frac_or_le _ _).trans (add_le_add_right ih _))
    intro b hb
    obtain ⟨x, hx, h⟩ := hb
    rcases mem_insert.1 hx with rfl | hx
    · exact Or.inl h
    · exact Or.inr ⟨x, hx, h⟩

theorem frac_le_one' (p : β → Prop) : frac p ≤ 1 := by
  classical
  unfold frac
  rcases Nat.eq_zero_or_pos (Fintype.card β) with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast card_le_univ _

end Frac

section Mean

variable {β : Type} [Fintype β]

theorem mean_indicator (p : β → Prop) [DecidablePred p] :
    mean (fun b ↦ if p b then (1 : ℝ) else 0) = frac p := by
  unfold mean frac
  rw [sum_boole]
  congr

theorem mean_sum' {ι : Type*} (s : Finset ι) (X : ι → β → ℝ) :
    mean (fun b ↦ ∑ j ∈ s, X j b) = ∑ j ∈ s, mean (X j) := by
  unfold mean
  rw [sum_comm, sum_div]

theorem mean_mono' {X Y : β → ℝ} (h : ∀ b, X b ≤ Y b) : mean X ≤ mean Y :=
  div_le_div_of_nonneg_right (sum_le_sum fun b _ ↦ h b) (Nat.cast_nonneg _)

theorem mean_add' (X Y : β → ℝ) : mean (fun b ↦ X b + Y b) = mean X + mean Y := by
  unfold mean
  rw [sum_add_distrib, add_div]

theorem mean_mul_const' (X : β → ℝ) (c : ℝ) : mean (fun b ↦ X b * c) = mean X * c := by
  unfold mean
  rw [← sum_mul, div_mul_eq_mul_div]

theorem mean_one' [Nonempty β] : mean (fun _ : β ↦ (1 : ℝ)) = 1 := by
  unfold mean
  have : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp [this]

end Mean

/-! ### Independent coordinates -/

section Coords

variable {Ω : Type} [Fintype Ω]

theorem sum_prod_coords {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} [Fintype α]
    (f : ι → α → ℝ) : ∑ ω : ι → α, ∏ i, f i (ω i) = ∏ i, ∑ x, f i x := by
  rw [prod_univ_sum, Fintype.piFinset_univ]

theorem mean_prod_coords {S : ℕ} (F : Fin S → Ω → ℝ) :
    mean (fun ω : Fin S → Ω ↦ ∏ k, F k (ω k)) = ∏ k, mean (F k) := by
  unfold mean
  rw [sum_prod_coords, Fintype.card_pi, prod_div_distrib]
  push_cast
  rfl

variable [Nonempty Ω]

theorem mean_coord {S : ℕ} (i : Fin S) (g : Ω → ℝ) :
    mean (fun ω : Fin S → Ω ↦ g (ω i)) = mean g := by
  classical
  have h := mean_prod_coords (fun k : Fin S ↦ if k = i then g else fun _ ↦ (1 : ℝ))
  have h1 : (fun ω : Fin S → Ω ↦ ∏ k, (if k = i then g else fun _ ↦ (1 : ℝ)) (ω k)) =
      fun ω ↦ g (ω i) := by
    funext ω
    rw [prod_eq_single i (fun k _ hk ↦ by simp [hk]) (by simp)]
    simp
  rw [h1] at h
  rw [h, prod_eq_single i (fun k _ hk ↦ by simp [hk, mean_one']) (by simp)]
  simp

theorem frac_coord {S : ℕ} (i : Fin S) (p : Ω → Prop) :
    frac (fun ω : Fin S → Ω ↦ p (ω i)) = frac p := by
  classical
  rw [← mean_indicator, ← mean_indicator]
  exact mean_coord i fun x ↦ if p x then (1 : ℝ) else 0

theorem mean_coord₂ {S : ℕ} {i j : Fin S} (hij : i ≠ j) (g h : Ω → ℝ) :
    mean (fun ω : Fin S → Ω ↦ g (ω i) * h (ω j)) = mean g * mean h := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : Fin S → Ω → ℝ,
      F = fun k ↦ if k = i then g else if k = j then h else fun _ ↦ 1 := ⟨_, rfl⟩
  have h0 := mean_prod_coords F
  have h1 : (fun ω : Fin S → Ω ↦ ∏ k, F k (ω k)) = fun ω ↦ g (ω i) * h (ω j) := by
    funext ω
    rw [prod_eq_mul i j hij (fun k _ hk ↦ by simp [hF, hk.1, hk.2]) (by simp) (by simp)]
    simp [hF, hij.symm]
  rw [h1] at h0
  rw [h0, prod_eq_mul i j hij (fun k _ hk ↦ by simp [hF, hk.1, hk.2, mean_one']) (by simp)
    (by simp)]
  simp [hF, hij.symm]

/-- The values of `u` partition the space. -/
theorem sum_frac_eq_one {γ : Type*} [Fintype γ] (u : Ω → γ) :
    ∑ c, frac (fun x ↦ u x = c) = 1 := by
  classical
  unfold frac
  rw [← sum_div, div_eq_one_iff_eq (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]
  have := card_eq_sum_card_fiberwise (f := u) (s := univ) (t := univ)
    (fun _ _ ↦ mem_coe.2 (mem_univ _))
  rw [card_univ] at this
  rw [← Nat.cast_sum]
  norm_cast
  convert this.symm

/-- **Collisions of two independent samples**: if each value of `u` has probability at most `w`,
then two distinct coordinates collide (up to a map `σ`) with probability at most `w`. -/
theorem frac_coord_collide_le {γ : Type*} [Finite γ] (u : Ω → γ) (σ : γ → γ)
    {w : ℝ} (hw : ∀ c, frac (fun x ↦ u x = c) ≤ w) {S : ℕ} {i j : Fin S} (hij : i ≠ j) :
    frac (fun ω : Fin S → Ω ↦ u (ω j) = σ (u (ω i))) ≤ w := by
  classical
  have := Fintype.ofFinite γ
  rw [← mean_indicator]
  have hsplit : (fun ω : Fin S → Ω ↦ if u (ω j) = σ (u (ω i)) then (1 : ℝ) else 0) =
      fun ω ↦ ∑ c, (if u (ω j) = σ c then (1 : ℝ) else 0) * (if u (ω i) = c then 1 else 0) := by
    funext ω
    rw [sum_eq_single (u (ω i)) (fun c _ hc ↦ by simp [Ne.symm hc]) (by simp)]
    simp
  rw [hsplit, mean_sum']
  have hterm : ∀ c, mean (fun ω : Fin S → Ω ↦
      (if u (ω j) = σ c then (1 : ℝ) else 0) * (if u (ω i) = c then 1 else 0)) ≤
      w * frac (fun x ↦ u x = c) := by
    intro c
    rw [mean_coord₂ hij.symm (fun x ↦ if u x = σ c then (1 : ℝ) else 0)
      (fun x ↦ if u x = c then (1 : ℝ) else 0), mean_indicator, mean_indicator]
    exact mul_le_mul_of_nonneg_right (hw _) (frac_nonneg' _)
  refine (sum_le_sum fun c _ ↦ hterm c).trans ?_
  rw [← mul_sum, sum_frac_eq_one, mul_one]

end Coords

/-! ### The expected number of dropped samples -/

section Drops

variable {Ω : Type} [Fintype Ω] [Nonempty Ω] {n : ℕ}

omit [Fintype Ω] [Nonempty Ω] in
theorem drops_le_sum (Δ : ℕ) (dec : Ω → Fin n × Fin n) {S : ℕ} (ω : Fin S → Ω) :
    (drops Δ dec ω : ℝ) ≤ nLoops (sampleEdge dec ω) + nReps (sampleEdge dec ω) +
      ∑ a : Fin n, ((nTouch (sampleEdge dec ω) a.1 - Δ : ℕ) : ℝ) := by
  have h := le_length_keptEdges_add Δ (range n) (sampleEdge dec ω)
    (fun i ↦ ⟨mem_range.2 (dec (ω i)).1.2, mem_range.2 (dec (ω i)).2.2⟩)
  rw [← Fin.sum_univ_eq_sum_range (fun a ↦ nTouch (sampleEdge dec ω) a - Δ) n] at h
  have h' : drops Δ dec ω ≤ nLoops (sampleEdge dec ω) + nReps (sampleEdge dec ω) +
      ∑ a : Fin n, (nTouch (sampleEdge dec ω) a.1 - Δ) := by
    unfold drops keptS
    omega
  exact_mod_cast h'

omit [Fintype Ω] [Nonempty Ω] in
theorem sampleEdge_loop_iff (dec : Ω → Fin n × Fin n) {S : ℕ} (ω : Fin S → Ω) (i : Fin S) :
    (sampleEdge dec ω i).1 = (sampleEdge dec ω i).2 ↔ (dec (ω i)).1 = (dec (ω i)).2 := by
  simp [sampleEdge, Fin.val_inj]

omit [Fintype Ω] [Nonempty Ω] in
theorem sampleEdge_eq_iff (dec : Ω → Fin n × Fin n) {S : ℕ} (ω : Fin S → Ω) (i j : Fin S) :
    sampleEdge dec ω j = sampleEdge dec ω i ↔ dec (ω j) = id (dec (ω i)) := by
  simp [sampleEdge, Prod.ext_iff, Fin.val_inj]

omit [Fintype Ω] [Nonempty Ω] in
theorem sampleEdge_eq_swap_iff (dec : Ω → Fin n × Fin n) {S : ℕ} (ω : Fin S → Ω) (i j : Fin S) :
    sampleEdge dec ω j = ((sampleEdge dec ω i).2, (sampleEdge dec ω i).1) ↔
      dec (ω j) = Prod.swap (dec (ω i)) := by
  simp [sampleEdge, Prod.ext_iff, Fin.val_inj]

/-- **Expected loops**. -/
theorem mean_nLoops_le (dec : Ω → Fin n × Fin n) {w : ℝ}
    (hw : ∀ e, frac (fun x ↦ dec x = e) ≤ w) (S : ℕ) :
    mean (fun ω : Fin S → Ω ↦ (nLoops (sampleEdge dec ω) : ℝ)) ≤ S * (n * w) := by
  classical
  have h1 : (fun ω : Fin S → Ω ↦ (nLoops (sampleEdge dec ω) : ℝ)) =
      fun ω ↦ ∑ i, if (dec (ω i)).1 = (dec (ω i)).2 then (1 : ℝ) else 0 := by
    funext ω
    unfold nLoops
    rw [card_filter]
    push_cast
    exact sum_congr rfl fun i _ ↦ by simp only [sampleEdge_loop_iff]
  rw [h1, mean_sum']
  have h2 : ∀ i : Fin S, mean (fun ω : Fin S → Ω ↦
      if (dec (ω i)).1 = (dec (ω i)).2 then (1 : ℝ) else 0) ≤ n * w := by
    intro i
    rw [mean_coord i (fun x ↦ if (dec x).1 = (dec x).2 then (1 : ℝ) else 0), mean_indicator]
    refine (frac_imp_le (q := fun x ↦ ∃ a ∈ (univ : Finset (Fin n)), dec x = (a, a)) ?_).trans
      ((frac_exists_le _ _).trans ?_)
    · intro x hx
      exact ⟨(dec x).1, mem_univ _, Prod.ext rfl hx.symm⟩
    · refine (sum_le_sum fun a _ ↦ hw (a, a)).trans ?_
      simp
  refine (sum_le_sum fun i _ ↦ h2 i).trans ?_
  simp

/-- **Expected repeats**. -/
theorem mean_nReps_le (dec : Ω → Fin n × Fin n) {w : ℝ}
    (hw : ∀ e, frac (fun x ↦ dec x = e) ≤ w) (S : ℕ) :
    mean (fun ω : Fin S → Ω ↦ (nReps (sampleEdge dec ω) : ℝ)) ≤ S * S * (2 * w) := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : Fin S → Fin S → (Fin S → Ω) → ℝ, F = fun i j ω ↦
      if j = i then 0 else (if dec (ω j) = id (dec (ω i)) then (1 : ℝ) else 0) +
        (if dec (ω j) = Prod.swap (dec (ω i)) then (1 : ℝ) else 0) := ⟨_, rfl⟩
  have hF0 : ∀ i j ω, 0 ≤ F i j ω := by
    intro i j ω
    rw [hF]
    dsimp only
    split_ifs <;> norm_num
  have h1 : ∀ ω : Fin S → Ω, (nReps (sampleEdge dec ω) : ℝ) ≤ ∑ i, ∑ j, F i j ω := by
    intro ω
    unfold nReps
    rw [card_filter]
    push_cast
    refine sum_le_sum fun i _ ↦ ?_
    split_ifs with h
    · obtain ⟨j, hj, hrep⟩ := h
      refine le_trans ?_ (single_le_sum (fun j _ ↦ hF0 i j ω) (mem_univ j))
      rw [hF]
      dsimp only
      simp only [ne_of_lt hj, ↓reduceIte]
      rcases hrep with hrep | hrep
      · rw [sampleEdge_eq_iff] at hrep
        simp only [hrep, ↓reduceIte]
        split_ifs <;> norm_num
      · rw [sampleEdge_eq_swap_iff] at hrep
        simp only [hrep, ↓reduceIte]
        split_ifs <;> norm_num
    · exact sum_nonneg fun j _ ↦ hF0 i j ω
  refine (mean_mono' h1).trans ?_
  rw [mean_sum']
  have h2 : ∀ i j, mean (F i j) ≤ 2 * w := by
    intro i j
    have hw0 : 0 ≤ w := (frac_nonneg' _).trans (hw (dec (Classical.arbitrary Ω)))
    rw [hF]
    by_cases hji : j = i
    · simp only [hji, ↓reduceIte]
      unfold mean
      simp only [sum_const_zero, zero_div]
      linarith
    · simp only [hji, ↓reduceIte]
      rw [mean_add', mean_indicator, mean_indicator]
      have := frac_coord_collide_le dec id hw (Ne.symm hji)
      have := frac_coord_collide_le dec Prod.swap hw (Ne.symm hji)
      linarith
  have h3 : ∀ i, mean (fun ω : Fin S → Ω ↦ ∑ j, F i j ω) ≤ S * (2 * w) := by
    intro i
    rw [mean_sum']
    refine (sum_le_sum fun j _ ↦ h2 i j).trans ?_
    simp
  refine (sum_le_sum fun i _ ↦ h3 i).trans ?_
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf
  rfl

/-- `y^m / m! ≤ (5/6)^m` for `m ≥ 10 y / 3`, since `m! ≥ (m/e)^m`. -/
theorem pow_div_factorial_le_of_le {y : ℝ} (hy : 0 ≤ y) {m : ℕ} (hm : 10 * y ≤ 3 * m) :
    y ^ m / m.factorial ≤ (5 / 6 : ℝ) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
  have h1 : (m : ℝ) ^ m / m.factorial ≤ Real.exp 1 ^ m := by
    rw [← Real.exp_nat_mul, mul_one]
    exact Real.pow_div_factorial_le_exp _ hmr.le m
  have h2 : y ^ m / m.factorial = (y / m) ^ m * ((m : ℝ) ^ m / m.factorial) := by
    rw [div_pow]
    field_simp
  have hym : y / m ≤ 3 / 10 := by
    rw [div_le_iff₀ hmr]
    linarith
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hyme : y / m * Real.exp 1 ≤ 5 / 6 := by
    have := mul_le_mul hym he.le he0.le (by norm_num)
    linarith
  rw [h2]
  calc (y / m) ^ m * ((m : ℝ) ^ m / m.factorial) ≤ (y / m) ^ m * Real.exp 1 ^ m :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (y / m * Real.exp 1) ^ m := (mul_pow _ _ _).symm
    _ ≤ (5 / 6) ^ m := pow_le_pow_left₀ (by positivity) hyme m

theorem natSub_cast_eq_sum (T Δ S : ℕ) (hT : T ≤ S) :
    ((T - Δ : ℕ) : ℝ) = ∑ k ∈ range S, if Δ + 1 + k ≤ T then (1 : ℝ) else 0 := by
  rw [sum_boole]
  have : (range S).filter (fun k ↦ Δ + 1 + k ≤ T) = range (T - Δ) := by
    ext k
    simp only [mem_filter, mem_range]
    omega
  rw [this, card_range]

theorem geom_five_sixths_le (S : ℕ) : ∑ k ∈ range S, (5 / 6 : ℝ) ^ k ≤ 6 := by
  rw [geom_sum_eq (by norm_num)]
  have : (0 : ℝ) ≤ (5 / 6) ^ S := by positivity
  rw [div_le_iff_of_neg (by norm_num)]
  linarith

/-- **Expected overflow at a vertex**: the samples at `a` beyond the first `Δ`. -/
theorem mean_overflow_le (dec : Ω → Fin n × Fin n) (a : Fin n) {D Δ S : ℕ} (hΔ : 10 * D ≤ Δ)
    (hS : (S : ℝ) * frac (fun x ↦ (dec x).1 = a ∨ (dec x).2 = a) ≤ 3 * D) :
    mean (fun ω : Fin S → Ω ↦ ((nTouch (sampleEdge dec ω) a.1 - Δ : ℕ) : ℝ)) ≤ 6 := by
  classical
  have hT : ∀ ω : Fin S → Ω, nTouch (sampleEdge dec ω) a.1 =
      (univ.filter fun i ↦ (dec (ω i)).1 = a ∨ (dec (ω i)).2 = a).card := by
    intro ω
    unfold nTouch
    congr 1
  have hTS : ∀ ω : Fin S → Ω,
      (univ.filter fun i ↦ (dec (ω i)).1 = a ∨ (dec (ω i)).2 = a).card ≤ S := by
    intro ω
    exact (card_le_univ _).trans (by simp)
  have h1 : (fun ω : Fin S → Ω ↦ ((nTouch (sampleEdge dec ω) a.1 - Δ : ℕ) : ℝ)) =
      fun ω ↦ ∑ k ∈ range S, if Δ + 1 + k ≤
        (univ.filter fun i ↦ (dec (ω i)).1 = a ∨ (dec (ω i)).2 = a).card then (1 : ℝ) else 0 := by
    funext ω
    rw [hT, natSub_cast_eq_sum _ _ _ (hTS ω)]
  rw [h1, mean_sum']
  have hp0 : 0 ≤ (S : ℝ) * frac (fun x ↦ (dec x).1 = a ∨ (dec x).2 = a) :=
    mul_nonneg (Nat.cast_nonneg _) (frac_nonneg' _)
  have h2 : ∀ k ∈ range S, mean (fun ω : Fin S → Ω ↦ if Δ + 1 + k ≤
      (univ.filter fun i ↦ (dec (ω i)).1 = a ∨ (dec (ω i)).2 = a).card then (1 : ℝ) else 0) ≤
      (5 / 6 : ℝ) ^ k := by
    intro k _
    rw [mean_indicator]
    refine (frac_count_ge_le (fun x ↦ (dec x).1 = a ∨ (dec x).2 = a) S (Δ + 1 + k)).trans ?_
    calc (S * frac (fun x ↦ (dec x).1 = a ∨ (dec x).2 = a)) ^ (Δ + 1 + k) /
          ((Δ + 1 + k).factorial : ℝ) ≤ (3 * D : ℝ) ^ (Δ + 1 + k) / (Δ + 1 + k).factorial :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ hp0 hS _) (Nat.cast_nonneg _)
      _ ≤ (5 / 6 : ℝ) ^ (Δ + 1 + k) := by
          apply pow_div_factorial_le_of_le (by positivity)
          have : (10 * D : ℝ) ≤ Δ := by exact_mod_cast hΔ
          push_cast
          linarith
      _ ≤ (5 / 6 : ℝ) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  exact (sum_le_sum h2).trans (geom_five_sixths_le S)

/-- **The expected number of dropped samples** is at most `9 n`. -/
theorem mean_drops_le {D Δ : ℕ} (hD : 1 ≤ D) (hΔ : 10 * D ≤ Δ) (dec : Ω → Fin n × Fin n)
    (htouch : ∀ a, frac (fun x ↦ (dec x).1 = a ∨ (dec x).2 = a) ≤ 3 / n)
    (hmax : ∀ e, frac (fun x ↦ dec x = e) ≤ 1 / (n * D ^ 2)) :
    mean (fun ω : Fin (n * D) → Ω ↦ (drops Δ dec ω : ℝ)) ≤ 9 * n := by
  have hn : 0 < n := Fin.pos (dec (Classical.arbitrary Ω)).1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h1 := mean_mono' (drops_le_sum (n := n) Δ dec (S := n * D))
  rw [mean_add', mean_add', mean_sum'] at h1
  have hL := mean_nLoops_le dec hmax (n * D)
  have hR := mean_nReps_le dec hmax (n * D)
  have hT : ∀ a : Fin n, mean (fun ω : Fin (n * D) → Ω ↦
      ((nTouch (sampleEdge dec ω) a.1 - Δ : ℕ) : ℝ)) ≤ 6 := by
    intro a
    refine mean_overflow_le dec a hΔ ?_
    calc ((n * D : ℕ) : ℝ) * frac (fun x ↦ (dec x).1 = a ∨ (dec x).2 = a) ≤
        ((n * D : ℕ) : ℝ) * (3 / n) := mul_le_mul_of_nonneg_left (htouch a) (Nat.cast_nonneg _)
      _ = 3 * D := by push_cast; field_simp
  have hT' := sum_le_sum fun a (_ : a ∈ (univ : Finset (Fin n))) ↦ hT a
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hT'
  have hLe : ((n * D : ℕ) : ℝ) * (n * (1 / (n * D ^ 2))) ≤ n := by
    push_cast
    rw [show (n : ℝ) * D * (n * (1 / (n * D ^ 2))) = n / D by field_simp]
    exact div_le_self hnr.le hDr
  have hRe : ((n * D : ℕ) : ℝ) * ((n * D : ℕ) : ℝ) * (2 * (1 / (n * D ^ 2))) = 2 * n := by
    push_cast
    field_simp
  linarith

/-- **Few samples are dropped** (Markov): at least `180 n` with probability at most `1/20`. -/
theorem frac_drops_ge_le {D Δ : ℕ} (hD : 1 ≤ D) (hΔ : 10 * D ≤ Δ) (dec : Ω → Fin n × Fin n)
    (htouch : ∀ a, frac (fun x ↦ (dec x).1 = a ∨ (dec x).2 = a) ≤ 3 / n)
    (hmax : ∀ e, frac (fun x ↦ dec x = e) ≤ 1 / (n * D ^ 2)) :
    frac (fun ω : Fin (n * D) → Ω ↦ (180 * n : ℝ) ≤ drops Δ dec ω) ≤ 1 / 20 := by
  have hn : 0 < n := Fin.pos (dec (Classical.arbitrary Ω)).1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  refine (frac_ge_le_mean _ (fun ω ↦ Nat.cast_nonneg _) (by positivity)).trans ?_
  rw [div_le_iff₀ (by positivity)]
  have := mean_drops_le hD hΔ dec htouch hmax
  linarith

end Drops

end BGHKLMM26.Hard
