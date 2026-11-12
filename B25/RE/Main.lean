module

public import B25.RE.RNO

/-!
# Theorem 1.5

`B25.re_of_partiallyRotated_main`: the statement of `B25.re_of_partiallyRotated` in
`B25/Challenge.lean`.

1. **RNO on signed tuples holds with high probability.** For each pair of tuples `a, b` of `s`
   signed coordinates of `S` and of `Sᶜ`, the vectors `tupleVec a` and `tupleVec b` are supported
   on `S` and on `Sᶜ` (`B25.tupleVec_eq_zero`), so partial rotation bounds the probability that
   their correlation exceeds `1/100` by `e^(-cn)`. There are at most `(2d)^(2s)` pairs, so
   `P(¬ TupleRNO X S s (1/100)) ≤ (2d)^(2s) e^(-cn)` (a union bound over a finite set; outer
   measures are subadditive, so no measurability is needed). This replaces the net argument of
   [B25, Lemma 1.11]: only these finitely many directions are needed.
2. **One level for all `S'`.** `γ_{S'}(X_S)` is random, so take one level for every `S'`:
   `s = ⌊c n / (4 log (2d))⌋` for `d ≥ 1`. Then `(2d)^(2s) ≤ e^(cn/2)`, and the failure
   probability is at most `e^(-cn/2)` (`c' = c/2`).
3. **On the good event** (RNO at level `s` and columns of norm `√n`, which fails only on a null
   set), every `S' ⊆ S` with `C |S'| log d ≤ n γ` (`γ = γ_{S'}(X_S)`) has `s γ ≥ 22500 |S'|`, so
   `B25.re_of_tupleRNO` applies. Indeed, for `S'` nonempty and `d ≥ 2`, `γ ≤ 1`
   (`B25.reConst_cols_le_one`) and `log (2d) ≤ 2 log d`, so
   `s γ ≥ c n γ / (4 log (2d)) - 1 ≥ c C |S'| / 8 - 1 ≥ 22500 |S'|` for `C = 8 · 22501 / c`.
   For `d ≤ 1`: either `S' = ∅` (trivial: both constants are `0`), or `S = S' = univ`, so `Sᶜ = ∅`
   and RNO holds at every level (there are no tuples of `Sᶜ` for `s ≥ 1`); apply
   `B25.re_of_tupleRNO` at a level `s ≥ 22500 |S'| / γ` (when `γ > 0`). For `n = 0` the bound
   `e^0 = 1` is trivial.
-/

@[expose] public section

namespace B25

open MeasureTheory Matrix

namespace TM

/-- Union bound over pairs of signed tuples: under partial rotation, RNO on signed tuples at
level `s` fails with (outer) probability at most `(2d)^(2s) e^(-δn)`. -/
theorem quorvTupleFail_le {Ω : Type*} [MeasurableSpace Ω] {n d : ℕ} {P : Measure Ω}
    {X : Ω → Matrix (Fin n) (Fin d) ℝ} {S : Finset (Fin d)} {ε δ : ℝ}
    (hP : PartiallyRotated P X S ε δ) (s : ℕ) :
    P {ω | ¬TupleRNO (X ω) S s ε} ≤
      ENNReal.ofReal ((2 * d : ℝ) ^ (2 * s) * Real.exp (-(δ * n))) := by
  classical
  let f : (Fin s → Fin d × Bool) × (Fin s → Fin d × Bool) → Set Ω := fun p ↦
    {ω | (∀ t, (p.1 t).1 ∈ S) ∧ (∀ t, (p.2 t).1 ∉ S) ∧
      ε < |corr (X ω *ᵥ tupleVec p.1) (X ω *ᵥ tupleVec p.2)|}
  have hf : ∀ p, P (f p) ≤ ENNReal.ofReal (Real.exp (-(δ * n))) := by
    rintro ⟨a, b⟩
    by_cases ha : ∀ t, (a t).1 ∈ S
    · by_cases hb : ∀ t, (b t).1 ∉ S
      · refine (measure_mono ?_).trans (hP (tupleVec a) (tupleVec b) ?_ ?_)
        · exact fun ω hω ↦ hω.2.2
        · exact fun j hj ↦ tupleVec_eq_zero ha hj
        · exact fun j hj ↦ tupleVec_eq_zero (T := Sᶜ) (fun t ↦ Finset.mem_compl.2 (hb t))
            (by simpa using hj)
      · simp [f, hb]
    · simp [f, ha]
  have hsub : {ω | ¬TupleRNO (X ω) S s ε} ⊆ ⋃ p, f p := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, TupleRNO] at hω
    push Not at hω
    obtain ⟨a, b, ha, hb, h⟩ := hω
    exact Set.mem_iUnion.2 ⟨(a, b), ha, hb, h⟩
  calc P {ω | ¬TupleRNO (X ω) S s ε} ≤ P (⋃ p, f p) := measure_mono hsub
    _ ≤ ∑ p, P (f p) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : (Fin s → Fin d × Bool) × (Fin s → Fin d × Bool),
          ENNReal.ofReal (Real.exp (-(δ * n))) := Finset.sum_le_sum fun p _ ↦ hf p
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show (2 * d : ℝ) ^ (2 * s) = (((2 * d) ^ (2 * s) : ℕ) : ℝ) by push_cast; ring,
        ENNReal.ofReal_natCast]
      congr 1
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      ring

/-- If every coordinate lies in `S`, RNO on signed tuples holds at every level: the tuples of
`Sᶜ` give the zero vector. -/
theorem quorvTupleRNO_of_forall_mem {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    {S : Finset (Fin d)} (hS : ∀ j, j ∈ S) (s : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    TupleRNO X S s ε := by
  intro a b _ hb
  have h0 : tupleVec b = 0 := by
    funext j
    exact tupleVec_eq_zero (T := ∅) (fun t ↦ absurd (hS _) (hb t)) (Finset.notMem_empty j)
  simpa [h0, corr] using hε

/-- The choice of the level: `(2d)^(2s) e^(-cn) ≤ e^(-cn/2)` when `4 s log (2d) ≤ cn`. -/
theorem quorvPowExp_le {c : ℝ} {n d s : ℕ} (hcn : 0 ≤ c * n)
    (hs : 4 * s * Real.log (2 * d) ≤ c * n) :
    (2 * d : ℝ) ^ (2 * s) * Real.exp (-(c * n)) ≤ Real.exp (-(c / 2 * n)) := by
  have hpow : (2 * d : ℝ) ^ (2 * s) ≤ Real.exp (c / 2 * n) := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd, Nat.cast_zero, mul_zero]
      exact (pow_le_one₀ le_rfl zero_le_one).trans (Real.one_le_exp (by linarith))
    · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 * d), ← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      push_cast
      linarith
  calc (2 * d : ℝ) ^ (2 * s) * Real.exp (-(c * n))
      ≤ Real.exp (c / 2 * n) * Real.exp (-(c * n)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = Real.exp (-(c / 2 * n)) := by rw [← Real.exp_add]; ring_nf

/-- The level `s = ⌊c n / (4 log (2d))⌋` satisfies `4 s log (2d) ≤ c n`. -/
theorem quorvLevel_le {c : ℝ} (hc : 0 < c) (n d : ℕ) :
    4 * (⌊c * n / (4 * Real.log (2 * d))⌋₊ : ℝ) * Real.log (2 * d) ≤ c * n := by
  have hcn : 0 ≤ c * n := by positivity
  rcases lt_or_ge 0 (Real.log (2 * d)) with hL | hL
  · have h := Nat.floor_le (div_nonneg hcn (by positivity : (0 : ℝ) ≤ 4 * Real.log (2 * d)))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  · have : 4 * (⌊c * n / (4 * Real.log (2 * d))⌋₊ : ℝ) * Real.log (2 * d) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hL
    linarith

/-- The deterministic step: on the good event (columns of norm `√n` and RNO on signed tuples at
level `⌊c n / (4 log (2d))⌋`), every `S' ⊆ S` with `C |S'| log d ≤ n γ_{S'}(X_S)`, where
`C = 8 · 22501 / c`, has `γ_{S'}(X) ≥ 0.9 γ_{S'}(X_S)`. -/
theorem quorvGood {c : ℝ} (hc : 0 < c) {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    {S S' : Finset (Fin d)} (hX : HasNormalizedColumns X)
    (hR : TupleRNO X S ⌊c * n / (4 * Real.log (2 * d))⌋₊ (1 / 100)) (hS' : S' ⊆ S)
    (h : 8 * 22501 / c * S'.card * Real.log d ≤ n * reConst (cols X S) (S'.subtype (· ∈ S))) :
    9 / 10 * reConst (cols X S) (S'.subtype (· ∈ S)) ≤ reConst X S' := by
  set γ := reConst (cols X S) (S'.subtype (· ∈ S)) with hγ
  have hγ0 : 0 ≤ γ := reConst_nonneg _ _
  rcases S'.eq_empty_or_nonempty with hemp | hne
  · have h0 : γ = 0 := by
      rw [hγ, hemp, Finset.subtype_eq_empty.2 (fun x _ ↦ Finset.notMem_empty x), reConst_empty]
    rw [h0, mul_zero]
    exact reConst_nonneg _ _
  rcases le_or_gt d 1 with hd | hd
  · have hall : ∀ j, j ∈ S := by
      obtain ⟨j0, hj0⟩ := hne
      intro j
      have hj : j = j0 := Fin.ext (by have := j.isLt; have := j0.isLt; omega)
      exact hj ▸ hS' hj0
    rcases hγ0.eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      exact reConst_nonneg _ _
    · refine re_of_tupleRNO hX
        (quorvTupleRNO_of_forall_mem X hall ⌈22500 * S'.card / γ⌉₊ (by norm_num)) hS' ?_
      calc 22500 * (S'.card : ℝ) = 22500 * S'.card / γ * γ := by field_simp
        _ ≤ ⌈22500 * S'.card / γ⌉₊ * γ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hpos.le
  · have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hlog : 0 < Real.log d := Real.log_pos (by linarith)
    have hk : (1 : ℝ) ≤ S'.card := by exact_mod_cast hne.card_pos
    have hC : 0 < 8 * 22501 / c := by positivity
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, Nat.cast_zero, zero_mul] at h
        have := mul_pos (mul_pos hC (by linarith : (0 : ℝ) < S'.card)) hlog
        linarith
      · exact h0
    have hγ1 : γ ≤ 1 := reConst_cols_le_one hn hX hS' hne
    have hLpos : 0 < Real.log (2 * d) := Real.log_pos (by linarith)
    have hL : Real.log (2 * d) ≤ 2 * Real.log d := by
      rw [two_mul (Real.log d), ← Real.log_mul (by positivity) (by positivity)]
      exact Real.log_le_log (by positivity) (by nlinarith)
    refine re_of_tupleRNO hX hR hS' ?_
    set L := Real.log (2 * d) with hLdef
    have hfl : c * n / (4 * L) - 1 ≤ (⌊c * n / (4 * L)⌋₊ : ℝ) := (Nat.sub_one_lt_floor _).le
    have hcC : c * (8 * 22501 / c * S'.card * Real.log d) = 8 * 22501 * S'.card * Real.log d := by
      field_simp
    have h2 : 8 * 22501 * S'.card * Real.log d ≤ c * (n * γ) := by
      rw [← hcC]
      exact mul_le_mul_of_nonneg_left h hc.le
    have h3 : 4 * 22501 * S'.card * L ≤ 8 * 22501 * S'.card * Real.log d := by
      have : 0 ≤ (S'.card : ℝ) := by positivity
      nlinarith
    have h1 : 22501 * S'.card ≤ c * n * γ / (4 * L) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    calc 22500 * (S'.card : ℝ) ≤ 22501 * S'.card - 1 := by linarith
      _ ≤ c * n * γ / (4 * L) - γ := by linarith
      _ = (c * n / (4 * L) - 1) * γ := by ring
      _ ≤ ⌊c * n / (4 * L)⌋₊ * γ := mul_le_mul_of_nonneg_right hfl hγ0

end TM

/-- **Theorem 1.5** of [B25]: the statement of `B25.re_of_partiallyRotated`. -/
theorem re_of_partiallyRotated_main :
    ∀ c : ℝ, 0 < c → ∃ C c' : ℝ, 0 < C ∧ 0 < c' ∧
      ∀ (n d : ℕ) (S : Finset (Fin d)) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (X : Ω → Matrix (Fin n) (Fin d) ℝ),
        (∀ᵐ ω ∂P, HasNormalizedColumns (X ω)) → PartiallyRotated P X S (1 / 100) c →
        P {ω | ∃ S' ⊆ S,
            C * S'.card * Real.log d ≤ n * reConst (cols (X ω) S) (S'.subtype (· ∈ S)) ∧
              reConst (X ω) S' < 9 / 10 * reConst (cols (X ω) S) (S'.subtype (· ∈ S))} ≤
          ENNReal.ofReal (Real.exp (-(c' * n))) := by
  intro c hc
  refine ⟨8 * 22501 / c, c / 2, by positivity, by positivity, ?_⟩
  intro n d S Ω _ P _ X hX hP
  have hsub : {ω | ∃ S' ⊆ S,
      8 * 22501 / c * S'.card * Real.log d ≤ n * reConst (cols (X ω) S) (S'.subtype (· ∈ S)) ∧
        reConst (X ω) S' < 9 / 10 * reConst (cols (X ω) S) (S'.subtype (· ∈ S))} ⊆
      {ω | ¬HasNormalizedColumns (X ω)} ∪
        {ω | ¬TupleRNO (X ω) S ⌊c * n / (4 * Real.log (2 * d))⌋₊ (1 / 100)} := by
    rintro ω ⟨S', hS', h1, h2⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
    exact (TM.quorvGood hc (X ω) hcon.1 hcon.2 hS' h1).not_gt h2
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ = P {ω | ¬TupleRNO (X ω) S ⌊c * n / (4 * Real.log (2 * d))⌋₊ (1 / 100)} := by
        rw [ae_iff.1 hX, zero_add]
    _ ≤ _ := TM.quorvTupleFail_le hP _
    _ ≤ _ := ENNReal.ofReal_le_ofReal
        (TM.quorvPowExp_le (by positivity) (by exact_mod_cast TM.quorvLevel_le hc n d))

end B25
