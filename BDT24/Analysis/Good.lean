module

public import BDT24.Analysis.Exact

/-!
# The good events and their probabilities

* **Own samples** (`BDT24.Analysis.Samp`): every coordinate is at most `rad n m` and not within
  `2^(-(n+m+4))` of a multiple of `2^(-q)`; then the own sample is the quantization of the
  Gaussian rows (`BDT24.Analysis.ownCells_eq`). It fails with probability at most
  `C exp(-n/10⁶)` (`BDT24.Analysis.prob_not_samp`), by the tails and the anti-concentration of
  `BDT24.Prob.Tail` with `T = n + m + 1`, uniformly in `m` and `q`.
* **A planted and a null sample** (`BDT24.Analysis.GoodP`): the planted coordinates are at most
  `rad n (d+1)`, the null sample is good for own samples, the responses are right
  (`BDT24.Analysis.RespOK`, failing only near a multiple of `2^(-p)`, for `q ≥ p + n + 2`), and
  the two statistics of the test concentrate (`BDT24.Prob.chi_upper`, `BDT24.Prob.chi_lower` with
  the laws `BDT24.Prob.law_noiseStat`, `BDT24.Prob.law_otherStat`). It fails with probability at
  most `C exp(-n/10⁶)` (`BDT24.Analysis.prob_not_goodP`).
-/

@[expose] public section

namespace BDT24.Analysis

open MeasureTheory ProbabilityTheory BDT24.Alg BDT24.Prob

/-- Every coordinate is at most `R` in absolute value. -/
def Tails (R : ℝ) {n m : ℕ} (z : Fin n → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ i j, |z i j| ≤ R

/-- **A good null sample for own samples**: every coordinate is at most `rad n m` and not near a
multiple of `2^(-q)`. -/
def Samp (q n m : ℕ) (g : Fin n → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ i j, |g i j| ≤ rad n m ∧ ¬ NearInt ((2 : ℝ) ^ q * g i j) (1 / 2 ^ (n + m + 4))

/-- **A good pair of a planted and a null sample.** -/
def GoodP (n d p q : ℕ) (v : Fin d → SignType)
    (zg : (Fin n → EuclideanSpace ℝ (Fin (d + 1))) × (Fin n → EuclideanSpace ℝ (Fin (d + 1)))) :
    Prop :=
  Tails (rad n (d + 1)) zg.1 ∧ Samp q n (d + 1) zg.2 ∧ RespOK p q zg.1 zg.2 ∧
    ∑ i, noiseStat d v (zg.1 i) ^ 2 ≤ 51 / 100 * n ∧
    98 / 100 * n ≤ ∑ i, otherStat d v (zg.1 i, zg.2 i) ^ 2

namespace GD

/-! ### Elementary bounds -/

/-- `x³ e^{-x/4} ≤ 3072 e^{-x/8}`, from `(x/8)³/3! ≤ e^{x/8}`. -/
theorem cube_mul_exp_le {x : ℝ} (hx : 0 ≤ x) :
    x ^ 3 * Real.exp (-x / 4) ≤ 3072 * Real.exp (-x / 8) := by
  have h := Real.pow_div_factorial_le_exp (x / 8) (by positivity) 3
  norm_num [Nat.factorial] at h
  have he : Real.exp (-x / 8) = Real.exp (x / 8) * Real.exp (-x / 4) := by
    rw [← Real.exp_add]
    ring_nf
  rw [he]
  have h4 : 0 < Real.exp (-x / 4) := Real.exp_pos _
  nlinarith

/-- `2^(-s) ≤ e^{-s/4}`, as `1/2 ≤ 3/4 ≤ e^{-1/4}`. -/
theorem inv_two_pow_le (s : ℕ) : 1 / (2 : ℝ) ^ s ≤ Real.exp (-(s : ℝ) / 4) := by
  have h : (1 / 2 : ℝ) ≤ Real.exp (-1 / 4) := by
    linarith [Real.add_one_le_exp (-1 / 4)]
  calc 1 / (2 : ℝ) ^ s = (1 / 2) ^ s := by rw [one_div_pow]
    _ ≤ Real.exp (-1 / 4) ^ s := pow_le_pow_left₀ (by norm_num) h s
    _ = Real.exp (-(s : ℝ) / 4) := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- `e^{-R²/4} ≤ e^{-R/4}` for `R ≥ 1`. -/
theorem exp_sq_le {R : ℝ} (hR : 1 ≤ R) : Real.exp (-R ^ 2 / 4) ≤ Real.exp (-R / 4) :=
  Real.exp_le_exp.2 (by nlinarith)

/-- A union bound with `N ≤ R²` terms of size at most `c R e^{-R/4}` is at most
`3072 c e^{-n/10⁶}` for `n ≤ R`. -/
theorem count_bound {N n : ℕ} {R c b : ℝ} (hR : 1 ≤ R) (hN : (N : ℝ) ≤ R ^ 2) (hc : 0 ≤ c)
    (hb : b ≤ c * R * Real.exp (-R / 4)) (hn : (n : ℝ) ≤ R) :
    N * b ≤ 3072 * c * Real.exp (-(n : ℝ) / 1000000) := by
  have he : 0 ≤ c * R * Real.exp (-R / 4) := by positivity
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hexp := Real.exp_le_exp.2 (show -R / 8 ≤ -(n : ℝ) / 1000000 by linarith)
  calc (N : ℝ) * b ≤ R ^ 2 * (c * R * Real.exp (-R / 4)) :=
        (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg N)).trans
          (mul_le_mul_of_nonneg_right hN he)
    _ = c * (R ^ 3 * Real.exp (-R / 4)) := by ring
    _ ≤ c * (3072 * Real.exp (-R / 8)) :=
        mul_le_mul_of_nonneg_left (cube_mul_exp_le (by linarith)) hc
    _ ≤ c * (3072 * Real.exp (-(n : ℝ) / 1000000)) := by gcongr
    _ = _ := by ring

/-- The grid term of `BDT24.Prob.nearInt_le`: `(2aR + 3)(2η/a) ≤ 10 R E` for `a, R ≥ 1` and
`0 ≤ η ≤ E`. -/
theorem grid_le {a R η E : ℝ} (ha : 1 ≤ a) (hR : 1 ≤ R) (hη0 : 0 ≤ η) (hηE : η ≤ E) :
    (2 * a * R + 3) * (2 * η / a) ≤ 10 * R * E := by
  have ha0 : 0 < a := by linarith
  have h1 : (2 * a * R + 3) * (2 * η / a) = 4 * R * η + 6 * η / a := by
    field_simp
    ring
  have h2 : 6 * η / a ≤ 6 * η := div_le_self (by positivity) ha
  rw [h1]
  nlinarith

/-! ### Laws through measure-preserving maps -/

/-- An upper bound through a measure-preserving map, for any set. -/
theorem real_le_of_mp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [IsFiniteMeasure ν] {f : α → β} (hf : MeasurePreserving f μ ν)
    {s : Set β} {t : Set α} (ht : t ⊆ f ⁻¹' s) : μ.real t ≤ ν.real s := by
  have h1 : μ t ≤ ν s := (measure_mono ht).trans
    (hf.map_eq ▸ Measure.le_map_apply hf.measurable.aemeasurable s)
  exact ENNReal.toReal_mono (measure_ne_top ν s) h1

/-- A coordinate of Gaussian rows is standard Gaussian. -/
theorem mp_coord (n m : ℕ) (i : Fin n) (j : Fin m) :
    MeasurePreserving (fun g : Fin n → EuclideanSpace ℝ (Fin m) ↦ g i j) (gRows n m)
      (gaussianReal 0 1) := by
  have h := measurePreserving_eval_multivariateGaussian (μ := 0)
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosSemidef.one (i := j)
  have e : gaussianReal ((0 : EuclideanSpace ℝ (Fin m)) j)
      ((1 : Matrix (Fin m) (Fin m) ℝ) j j).toNNReal = gaussianReal 0 1 := by simp
  rw [e] at h
  exact h.comp (measurePreserving_eval _ i)

/-! ### Own samples -/

/-- One coordinate of Gaussian rows is too large or near the grid with probability at most
`14 R e^{-R/4}`, `R = rad n m`. -/
theorem coord_bad_le (n m q : ℕ) (ij : Fin n × Fin m) :
    (gRows n m).real ({g | (rad n m : ℝ) < |g ij.1 ij.2|} ∪
        {g | NearInt ((2 : ℝ) ^ q * g ij.1 ij.2) (1 / 2 ^ (n + m + 4))}) ≤
      14 * (rad n m : ℝ) * Real.exp (-(rad n m : ℝ) / 4) := by
  set R : ℝ := (rad n m : ℝ) with hRdef
  have hR1 : 1 ≤ R := by
    rw [hRdef]
    exact_mod_cast Nat.le_add_left 1 (n + m)
  have hmp := mp_coord n m ij.1 ij.2
  have h1 : (gRows n m).real {g | R < |g ij.1 ij.2|} ≤ 2 * Real.exp (-R ^ 2 / 4) :=
    (real_le_of_mp hmp (s := {x | R < |x|}) fun _ h ↦ h).trans
      (gauss_tail 1 (by norm_num) (by linarith))
  have h2 : (gRows n m).real {g | NearInt ((2 : ℝ) ^ q * g ij.1 ij.2) (1 / 2 ^ (n + m + 4))} ≤
      2 * Real.exp (-R ^ 2 / 4) +
        (2 * 2 ^ q * R + 3) * (2 * (1 / 2 ^ (n + m + 4)) / 2 ^ q) :=
    (real_le_of_mp hmp (s := {y | NearInt ((2 : ℝ) ^ q * y) (1 / 2 ^ (n + m + 4))})
      fun _ h ↦ h).trans
      (nearInt_le 1 (by norm_num) (by norm_num) (one_le_pow₀ (by norm_num)) (by positivity)
        (by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)) (by linarith))
  have hη : (1 : ℝ) / 2 ^ (n + m + 4) ≤ Real.exp (-R / 4) := by
    refine le_trans ?_ (inv_two_pow_le (rad n m))
    gcongr
    · norm_num
    · simp only [rad]
      omega
  have hg := grid_le (a := (2 : ℝ) ^ q) (one_le_pow₀ (by norm_num)) hR1 (by positivity) hη
  have he := exp_sq_le hR1
  have hE : 0 ≤ Real.exp (-R / 4) := (Real.exp_pos _).le
  have hRE : Real.exp (-R / 4) ≤ R * Real.exp (-R / 4) := le_mul_of_one_le_left hE hR1
  linarith [measureReal_union_le (μ := gRows n m) {g | R < |g ij.1 ij.2|}
    {g | NearInt ((2 : ℝ) ^ q * g ij.1 ij.2) (1 / 2 ^ (n + m + 4))}]

/-- **Own samples are good** except with probability `C exp(-n/10⁶)`. -/
theorem prob_not_samp_aux (n m q : ℕ) :
    (gRows n m).real {g | ¬ Samp q n m g} ≤ 3072 * 14 * Real.exp (-(n : ℝ) / 1000000) := by
  have hsub : {g | ¬ Samp q n m g} ⊆ ⋃ ij ∈ (Finset.univ : Finset (Fin n × Fin m)),
      ({g | (rad n m : ℝ) < |g ij.1 ij.2|} ∪
        {g | NearInt ((2 : ℝ) ^ q * g ij.1 ij.2) (1 / 2 ^ (n + m + 4))}) := by
    intro g hg
    simp only [Samp, not_forall, not_and_or, not_not, not_le, Set.mem_ofPred_eq] at hg
    obtain ⟨i, j, h⟩ := hg
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, Finset.mem_univ,
      exists_true_left]
    exact ⟨(i, j), h⟩
  have hR1 : (1 : ℝ) ≤ (rad n m : ℝ) := by exact_mod_cast Nat.le_add_left 1 (n + m)
  have hN : ((Fintype.card (Fin n × Fin m) : ℕ) : ℝ) ≤ (rad n m : ℝ) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fin, rad]
    push_cast
    nlinarith
  calc (gRows n m).real {g | ¬ Samp q n m g}
      ≤ (gRows n m).real (⋃ ij ∈ (Finset.univ : Finset (Fin n × Fin m)),
          ({g | (rad n m : ℝ) < |g ij.1 ij.2|} ∪
            {g | NearInt ((2 : ℝ) ^ q * g ij.1 ij.2) (1 / 2 ^ (n + m + 4))})) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ ij : Fin n × Fin m, (gRows n m).real ({g | (rad n m : ℝ) < |g ij.1 ij.2|} ∪
          {g | NearInt ((2 : ℝ) ^ q * g ij.1 ij.2) (1 / 2 ^ (n + m + 4))}) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _ij : Fin n × Fin m, 14 * (rad n m : ℝ) * Real.exp (-(rad n m : ℝ) / 4) :=
        Finset.sum_le_sum fun ij _ ↦ coord_bad_le n m q ij
    _ = ((Fintype.card (Fin n × Fin m) : ℕ) : ℝ) *
          (14 * (rad n m : ℝ) * Real.exp (-(rad n m : ℝ) / 4)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := count_bound hR1 hN (by norm_num) le_rfl
        (by simp only [rad]; push_cast; linarith)

/-! ### A planted and a null sample -/

/-- Samples of `n` points of `ℝ^{d+1}`. -/
abbrev Sm (n d : ℕ) : Type := Fin n → EuclideanSpace ℝ (Fin (d + 1))

/-- The law of a planted and a null sample. -/
noncomputable abbrev pairLaw (n d k : ℕ) (v : Fin d → SignType) : Measure (Sm n d × Sm n d) :=
  (Measure.pi fun _ : Fin n ↦ plantedLaw d k v).prod (gRows n (d + 1))

/-- A union bound for five sets. -/
theorem real_union5_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A B C D E : Set α) :
    μ.real (A ∪ B ∪ C ∪ D ∪ E) ≤ μ.real A + μ.real B + μ.real C + μ.real D + μ.real E := by
  linarith [measureReal_union_le (μ := μ) (A ∪ B ∪ C ∪ D) E,
    measureReal_union_le (μ := μ) (A ∪ B ∪ C) D, measureReal_union_le (μ := μ) (A ∪ B) C,
    measureReal_union_le (μ := μ) A B]

/-- A coordinate of the planted sample is Gaussian with a variance in `[1/2, 1]`. -/
theorem mp_fst_coord {n d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) (i : Fin n)
    (j : Fin (d + 1)) : ∃ σ2 : NNReal, (1 / 2 : ℝ) ≤ σ2 ∧ (σ2 : ℝ) ≤ 1 ∧
      MeasurePreserving (fun zg : Sm n d × Sm n d ↦ zg.1 i j) (pairLaw n d k v)
        (gaussianReal 0 σ2) := by
  obtain ⟨σ2, h1, h2, hmap⟩ := law_coord hv j
  refine ⟨σ2, h1, h2, ?_⟩
  have hj : MeasurePreserving (fun z : EuclideanSpace ℝ (Fin (d + 1)) ↦ z j) (plantedLaw d k v)
      (gaussianReal 0 σ2) := ⟨by fun_prop, hmap⟩
  exact (hj.comp (measurePreserving_eval (fun _ : Fin n ↦ plantedLaw d k v) i)).comp
    measurePreserving_fst

/-- The `i`-th planted and null points are a planted and a null point. -/
theorem mp_pair (n d k : ℕ) (v : Fin d → SignType) (i : Fin n) :
    MeasurePreserving (fun zg : Sm n d × Sm n d ↦ (zg.1 i, zg.2 i)) (pairLaw n d k v)
      ((plantedLaw d k v).prod (nullLaw (d + 1))) :=
  (measurePreserving_eval _ i).prod (measurePreserving_eval _ i)

/-- The planted coordinates are at most `rad n (d+1)` except with probability
`C exp(-n/10⁶)`. -/
theorem tails_bound {n d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) :
    (pairLaw n d k v).real {zg | ¬ Tails (rad n (d + 1)) zg.1} ≤
      3072 * 2 * Real.exp (-(n : ℝ) / 1000000) := by
  set R : ℝ := (rad n (d + 1) : ℝ) with hRdef
  have hR1 : 1 ≤ R := by
    rw [hRdef]
    exact_mod_cast Nat.le_add_left 1 (n + (d + 1))
  have hsub : {zg : Sm n d × Sm n d | ¬ Tails R zg.1} ⊆
      ⋃ ij ∈ (Finset.univ : Finset (Fin n × Fin (d + 1))), {zg | R < |zg.1 ij.1 ij.2|} := by
    intro zg hzg
    simp only [Tails, not_forall, not_le, Set.mem_ofPred_eq] at hzg
    obtain ⟨i, j, h⟩ := hzg
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_univ, exists_true_left]
    exact ⟨(i, j), h⟩
  have hone : ∀ ij : Fin n × Fin (d + 1),
      (pairLaw n d k v).real {zg | R < |zg.1 ij.1 ij.2|} ≤ 2 * R * Real.exp (-R / 4) := by
    intro ij
    obtain ⟨σ2, -, h2, hmp⟩ := mp_fst_coord hv ij.1 ij.2
    have h : (pairLaw n d k v).real {zg | R < |zg.1 ij.1 ij.2|} ≤ 2 * Real.exp (-R ^ 2 / 4) :=
      (real_le_of_mp hmp (s := {x | R < |x|}) fun _ h ↦ h).trans
        (gauss_tail σ2 (by linarith) (by linarith))
    have he := exp_sq_le hR1
    have hE : 0 ≤ Real.exp (-R / 4) := (Real.exp_pos _).le
    have hRE : Real.exp (-R / 4) ≤ R * Real.exp (-R / 4) := le_mul_of_one_le_left hE hR1
    linarith
  have hN : ((Fintype.card (Fin n × Fin (d + 1)) : ℕ) : ℝ) ≤ R ^ 2 := by
    simp only [hRdef, Fintype.card_prod, Fintype.card_fin, rad]
    push_cast
    nlinarith
  calc (pairLaw n d k v).real {zg | ¬ Tails R zg.1}
      ≤ (pairLaw n d k v).real (⋃ ij ∈ (Finset.univ : Finset (Fin n × Fin (d + 1))),
          {zg | R < |zg.1 ij.1 ij.2|}) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ ij : Fin n × Fin (d + 1), (pairLaw n d k v).real {zg | R < |zg.1 ij.1 ij.2|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _ij : Fin n × Fin (d + 1), 2 * R * Real.exp (-R / 4) :=
        Finset.sum_le_sum fun ij _ ↦ hone ij
    _ = ((Fintype.card (Fin n × Fin (d + 1)) : ℕ) : ℝ) * (2 * R * Real.exp (-R / 4)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := count_bound hR1 hN (by norm_num) le_rfl
        (by simp only [hRdef, rad]; push_cast; linarith)

/-- The null sample is good for own samples except with probability `C exp(-n/10⁶)`. -/
theorem samp_bound (n d k q : ℕ) (v : Fin d → SignType) :
    (pairLaw n d k v).real {zg | ¬ Samp q n (d + 1) zg.2} ≤
      3072 * 14 * Real.exp (-(n : ℝ) / 1000000) :=
  (real_le_of_mp measurePreserving_snd (s := {g | ¬ Samp q n (d + 1) g}) fun _ h ↦ h).trans
    (prob_not_samp_aux n (d + 1) q)

/-- The responses are right except with probability `C exp(-n/10⁶)`. -/
theorem resp_bound {n d k p q : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k)
    (hpq : p + n + 2 ≤ q) :
    (pairLaw n d k v).real {zg | ¬ RespOK p q zg.1 zg.2} ≤
      3072 * 12 * Real.exp (-(n : ℝ) / 1000000) := by
  set R : ℝ := (n : ℝ) + 1 with hRdef
  set η : ℝ := 2 / 2 ^ (q - p) with hηdef
  have hR1 : 1 ≤ R := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hsub : {zg : Sm n d × Sm n d | ¬ RespOK p q zg.1 zg.2} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin n)),
        {zg | NearInt ((2 : ℝ) ^ p * (√(2 / 3) * (zg.1 i 0 + zg.2 i 0))) η} := by
    intro zg hzg
    by_contra hc
    refine hzg (respOK_of (by omega) fun i hi ↦ hc ?_)
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_univ, exists_true_left]
    exact ⟨i, hi⟩
  have hη0 : 0 ≤ η := by positivity
  have hηn : η ≤ 1 / 2 ^ (n + 1) := by
    rw [hηdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 : ℝ) ^ (n + 2) ≤ 2 ^ (q - p) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc (2 : ℝ) * 2 ^ (n + 1) = 2 ^ (n + 2) := by ring
      _ ≤ 2 ^ (q - p) := this
      _ = 1 * 2 ^ (q - p) := (one_mul _).symm
  have hη1 : η ≤ 1 :=
    hηn.trans (by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num))
  have hηE : η ≤ Real.exp (-R / 4) := by
    refine hηn.trans ((inv_two_pow_le (n + 1)).trans_eq ?_)
    rw [hRdef]
    push_cast
    rfl
  set σ2 : NNReal := (2 / 3 * (((k : ℝ) + 1) / ((k : ℝ) + 2) + 1)).toNNReal with hσ
  have hx0 : 0 ≤ ((k : ℝ) + 1) / ((k : ℝ) + 2) := by positivity
  have hx1 : ((k : ℝ) + 1) / ((k : ℝ) + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hσe : (σ2 : ℝ) = 2 / 3 * (((k : ℝ) + 1) / ((k : ℝ) + 2) + 1) :=
    Real.coe_toNNReal _ (by positivity)
  have hr : MeasurePreserving
      (fun w : EuclideanSpace ℝ (Fin (d + 1)) × EuclideanSpace ℝ (Fin (d + 1)) ↦
        √(2 / 3) * (w.1 0 + w.2 0))
      ((plantedLaw d k v).prod (nullLaw (d + 1))) (gaussianReal 0 σ2) :=
    ⟨by fun_prop, law_resp hv⟩
  have hone : ∀ i : Fin n, (pairLaw n d k v).real
      {zg | NearInt ((2 : ℝ) ^ p * (√(2 / 3) * (zg.1 i 0 + zg.2 i 0))) η} ≤
        12 * R * Real.exp (-R / 4) := by
    intro i
    have h : (pairLaw n d k v).real
        {zg | NearInt ((2 : ℝ) ^ p * (√(2 / 3) * (zg.1 i 0 + zg.2 i 0))) η} ≤
          2 * Real.exp (-R ^ 2 / 4) + (2 * 2 ^ p * R + 3) * (2 * η / 2 ^ p) :=
      (real_le_of_mp (hr.comp (mp_pair n d k v i))
        (s := {y | NearInt ((2 : ℝ) ^ p * y) η}) fun _ h ↦ h).trans
        (nearInt_le σ2 (T := R) (by rw [hσe]; linarith) (by rw [hσe]; linarith)
          (one_le_pow₀ (by norm_num)) hη0 hη1 (by linarith))
    have hg := grid_le (a := (2 : ℝ) ^ p) (one_le_pow₀ (by norm_num)) hR1 hη0 hηE
    have he := exp_sq_le hR1
    have hE : 0 ≤ Real.exp (-R / 4) := (Real.exp_pos _).le
    have hRE : Real.exp (-R / 4) ≤ R * Real.exp (-R / 4) := le_mul_of_one_le_left hE hR1
    linarith
  have hN : ((Fintype.card (Fin n) : ℕ) : ℝ) ≤ R ^ 2 := by
    rw [Fintype.card_fin, hRdef]
    nlinarith
  calc (pairLaw n d k v).real {zg | ¬ RespOK p q zg.1 zg.2}
      ≤ (pairLaw n d k v).real (⋃ i ∈ (Finset.univ : Finset (Fin n)),
          {zg | NearInt ((2 : ℝ) ^ p * (√(2 / 3) * (zg.1 i 0 + zg.2 i 0))) η}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i : Fin n, (pairLaw n d k v).real
          {zg | NearInt ((2 : ℝ) ^ p * (√(2 / 3) * (zg.1 i 0 + zg.2 i 0))) η} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i : Fin n, 12 * R * Real.exp (-R / 4) := Finset.sum_le_sum fun i _ ↦ hone i
    _ = ((Fintype.card (Fin n) : ℕ) : ℝ) * (12 * R * Real.exp (-R / 4)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := count_bound hR1 hN (by norm_num) le_rfl (by linarith)

/-- The residuals of the planted sample are small except with probability `exp(-n/10⁵)`. -/
theorem noise_bound {n d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) :
    (pairLaw n d k v).real {zg | ¬ ∑ i, noiseStat d v (zg.1 i) ^ 2 ≤ 51 / 100 * n} ≤
      Real.exp (-(n : ℝ) / 100000) := by
  set σ2 : NNReal := (1 / 2 : ℝ).toNNReal with hσ
  have hσe : (σ2 : ℝ) = 1 / 2 := Real.coe_toNNReal _ (by norm_num)
  have hmeas : Measurable (noiseStat d v) := by
    unfold noiseStat
    fun_prop
  have hmp : MeasurePreserving (fun zg : Sm n d × Sm n d ↦ fun i ↦ noiseStat d v (zg.1 i))
      (pairLaw n d k v) (Measure.pi fun _ : Fin n ↦ gaussianReal 0 σ2) :=
    (measurePreserving_pi _ _ (f := fun _ ↦ noiseStat d v)
      fun _ ↦ ⟨hmeas, law_noiseStat hv⟩).comp measurePreserving_fst
  refine (real_le_of_mp hmp (s := {x | (51 / 50 : ℝ) * σ2 * n < ∑ i, x i ^ 2}) ?_).trans
    (chi_upper n σ2 (Real.toNNReal_pos.2 (by norm_num)))
  intro zg hzg
  have h := not_le.1 hzg
  change (51 / 50 : ℝ) * σ2 * n < ∑ i, noiseStat d v (zg.1 i) ^ 2
  rw [hσe]
  linarith

/-- The differences of the planted and the null sample are large except with probability
`exp(-n/10⁵)`. -/
theorem other_bound {n d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) :
    (pairLaw n d k v).real {zg | ¬ 98 / 100 * n ≤ ∑ i, otherStat d v (zg.1 i, zg.2 i) ^ 2} ≤
      Real.exp (-(n : ℝ) / 100000) := by
  set σ2 : NNReal := (1 + (k : ℝ) / (2 * ((k : ℝ) + 2))).toNNReal with hσ
  have hσe : (σ2 : ℝ) = 1 + (k : ℝ) / (2 * ((k : ℝ) + 2)) := Real.coe_toNNReal _ (by positivity)
  have hσ1 : 1 ≤ (σ2 : ℝ) := by
    rw [hσe]
    have : 0 ≤ (k : ℝ) / (2 * ((k : ℝ) + 2)) := by positivity
    linarith
  have hmeas : Measurable (otherStat d v) := by
    unfold otherStat
    fun_prop
  have hmp : MeasurePreserving ((fun w i ↦ otherStat d v (w i)) ∘
      (MeasurableEquiv.arrowProdEquivProdArrow (EuclideanSpace ℝ (Fin (d + 1)))
        (EuclideanSpace ℝ (Fin (d + 1))) (Fin n)).symm)
      (pairLaw n d k v) (Measure.pi fun _ : Fin n ↦ gaussianReal 0 σ2) :=
    (measurePreserving_pi _ _ (f := fun _ ↦ otherStat d v)
      fun _ ↦ ⟨hmeas, law_otherStat hv⟩).comp
      (MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow _ _ _ _ _))
  refine (real_le_of_mp hmp (s := {x | ∑ i, x i ^ 2 < (49 / 50 : ℝ) * σ2 * n}) ?_).trans
    (chi_lower n σ2 (NNReal.coe_pos.1 (by linarith)))
  intro zg hzg
  have h := not_le.1 hzg
  change ∑ i, otherStat d v (zg.1 i, zg.2 i) ^ 2 < (49 / 50 : ℝ) * σ2 * n
  have : (98 / 100 : ℝ) * n ≤ 49 / 50 * σ2 * n := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  linarith

end GD

open GD


/-- **Own samples are good** except with probability `C exp(-n/10⁶)`. -/
theorem prob_not_samp : ∃ C₂ : ℝ, ∀ n m q : ℕ,
    (gRows n m).real {g | ¬ Samp q n m g} ≤ C₂ * Real.exp (-(n : ℝ) / 1000000) :=
  ⟨3072 * 14, prob_not_samp_aux⟩

/-- **Planted and null samples are good** except with probability `C exp(-n/10⁶)`. -/
theorem prob_not_goodP : ∃ C₁ : ℝ, ∀ (n d k p q : ℕ) (v : Fin d → SignType),
    v ∈ spikeSigns d k → p + n + 2 ≤ q →
    ((Measure.pi fun _ : Fin n ↦ plantedLaw d k v).prod (gRows n (d + 1))).real
        {zg | ¬ GoodP n d p q v zg} ≤ C₁ * Real.exp (-(n : ℝ) / 1000000) := by
  refine ⟨3072 * 2 + 3072 * 14 + 3072 * 12 + 2, fun n d k p q v hv hpq ↦ ?_⟩
  change (pairLaw n d k v).real _ ≤ _
  have hsub : {zg | ¬ GoodP n d p q v zg} ⊆
      {zg : Sm n d × Sm n d | ¬ Tails (rad n (d + 1)) zg.1} ∪
        {zg | ¬ Samp q n (d + 1) zg.2} ∪ {zg | ¬ RespOK p q zg.1 zg.2} ∪
        {zg | ¬ ∑ i, noiseStat d v (zg.1 i) ^ 2 ≤ 51 / 100 * n} ∪
        {zg | ¬ 98 / 100 * n ≤ ∑ i, otherStat d v (zg.1 i, zg.2 i) ^ 2} := by
    intro zg hzg
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    simp only [GoodP, Set.mem_ofPred_eq] at hzg
    tauto
  have hexp : Real.exp (-(n : ℝ) / 100000) ≤ Real.exp (-(n : ℝ) / 1000000) :=
    Real.exp_le_exp.2 (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((real_union5_le _ _ _ _ _ _).trans ?_)
  linarith [tails_bound (n := n) hv, samp_bound n d k q v, resp_bound hv hpq,
    noise_bound (n := n) hv, other_bound (n := n) hv]

end BDT24.Analysis
