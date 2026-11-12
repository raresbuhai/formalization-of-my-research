module

public import BDT24.Analysis.Test
public import BDT24.Analysis.Good
public import BDT24.Alg.PolyTime

/-!
# The planted case

* **Rounds** (`BDT24.Analysis.output_false_le`): the algorithm says `false` only if some round
  fails, so with probability at most `rounds δ n` times the probability that one round fails
  (`1 - p^M ≤ M (1 - p)`).
* **One round on planted input** (`BDT24.Analysis.planted_calls`): a round fails only if one of
  its two tests does (`BDT24.Alg.coinProb_blockTest_false_le`). Its first test sees the input `z`
  and an own sample, which on a good null sample is the quantized null sample `g`
  (`BDT24.Analysis.ownCells_eq`); then the regression input is the `p`-bit input of the regression
  sample `pairMap(z, g)` (`BDT24.Analysis.slrInputOf_fwd`), whose law is that of sparse linear
  regression (`BDT24.Prob.pairMap_fwd`) on a bounded instance (`BDT24.Prob.bounded_fwd`). So the
  regression algorithm predicts well with probability at least `1 - δ`, and then the test is right
  (`BDT24.Analysis.test_fwd`), given that the output of the regression algorithm is short enough
  (`BDT24.Analysis.output_length_le`) for the precision `q ≥ (n + d + p + 2)^E₀`. The second test
  is the same with the pair swapped. So a round fails with probability at most
  `2 (δ + P(not good))`.
* **Helpers** (`BDT24.Analysis.PL`): generalities on coin probabilities; measurability of the
  integrands, which depend on the sample through its quantization, a point of a countable type
  (`BDT24.Analysis.PL.measurable_coinProb_slr`); the law of the regression sample of two
  independent samples (`BDT24.Analysis.PL.map_pairs`); and the arithmetic of the precision
  (`BDT24.Analysis.PL.prec_le`, with the exponent `BDT24.Analysis.PL.E0`).
-/

@[expose] public section

namespace BDT24.Analysis.PL

open MeasureTheory ProbabilityTheory BDT24.Alg BDT24.Prob

/-! ### Coin probabilities -/

/-- Coin probabilities are nonnegative. -/
theorem coinProb_nonneg (m : ℕ) (P : List Bool → Prop) : 0 ≤ coinProb m P := by
  unfold coinProb
  positivity

/-- Coin probabilities are at most `1`. -/
theorem coinProb_le_one (m : ℕ) (P : List Bool → Prop) : coinProb m P ≤ 1 := by
  classical
  unfold coinProb
  rw [div_le_one (by positivity)]
  have h := Fintype.card_subtype_le (fun r : Fin m → Bool ↦ P (List.ofFn r))
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  exact_mod_cast h

/-- Coin probabilities are monotone in the event, on strings of the right length. -/
theorem coinProb_mono {m : ℕ} {P P' : List Bool → Prop}
    (h : ∀ c : List Bool, c.length = m → P c → P' c) : coinProb m P ≤ coinProb m P' := by
  classical
  unfold coinProb
  gcongr
  exact Fintype.card_subtype_mono _ _ fun r ↦ h (List.ofFn r) (List.length_ofFn)

/-- A coin probability as an average of indicators. -/
theorem coinProb_eq_sum (m : ℕ) (P : List Bool → Prop) [DecidablePred P] :
    coinProb m P = (∑ r : Fin m → Bool, if P (List.ofFn r) then (1 : ℝ) else 0) / 2 ^ m := by
  unfold coinProb
  rw [Fintype.card_subtype, Finset.card_filter]
  push_cast
  rfl

/-! ### Measurability -/

/-- An event of the coins and a point that is measurable in the point for every coin string has
a measurable probability. -/
theorem measurable_coinProb {α : Type*} [MeasurableSpace α] (m : ℕ) (Q : List Bool → α → Prop)
    (hQ : ∀ c, MeasurableSet {a | Q c a}) : Measurable fun a ↦ coinProb m (fun c ↦ Q c a) := by
  classical
  simp_rw [coinProb_eq_sum]
  refine Measurable.div_const (Finset.measurable_sum _ fun r _ ↦ ?_) _
  exact Measurable.ite (hQ _) measurable_const measurable_const

/-- Quantization is measurable. -/
theorem measurable_quantize (p : ℕ) : Measurable (quantize p) := by
  unfold quantize
  exact Int.measurable_floor.comp (measurable_const.mul measurable_id)

/-- The quantized regression sample, in a countable type. -/
noncomputable def qS (p : ℕ) {n D : ℕ} (S : Fin n → EuclideanSpace ℝ (Fin D) × ℝ) :
    (Fin n → Fin D → ℤ) × (Fin n → ℤ) :=
  (fun j i ↦ quantize p ((S j).1 i), fun j ↦ quantize p (S j).2)

/-- The regression input of a quantized regression sample. -/
def mkI (k p : ℕ) {n D : ℕ} (w : (Fin n → Fin D → ℤ) × (Fin n → ℤ)) : SLRInput :=
  ⟨k, p, List.ofFn fun j ↦ List.ofFn fun i ↦ w.1 j i, List.ofFn fun j ↦ w.2 j⟩

/-- The regression input depends on the sample only through its quantization. -/
theorem slrInput_eq_mkI (k p : ℕ) {n D : ℕ} (S : Fin n → EuclideanSpace ℝ (Fin D) × ℝ) :
    slrInput k p S = mkI k p (qS p S) :=
  rfl

/-- The quantization of a regression sample is measurable. -/
theorem measurable_qS (p : ℕ) {n D : ℕ} : Measurable (qS p (n := n) (D := D)) := by
  unfold qS
  refine Measurable.prodMk ?_ ?_
  · refine Measurable.of_eval fun j ↦ Measurable.of_eval fun i ↦ ?_
    exact (measurable_quantize p).comp (by fun_prop)
  · refine Measurable.of_eval fun j ↦ ?_
    exact (measurable_quantize p).comp (by fun_prop)

/-- The probability over the coins of an event of the regression input, the coins and the
sample is measurable in the sample. -/
theorem measurable_coinProb_slr (k p : ℕ) {n D : ℕ} (T : SLRInput → ℕ)
    (Q : SLRInput → List Bool → (Fin n → EuclideanSpace ℝ (Fin D) × ℝ) → Prop)
    (hQ : ∀ I c, MeasurableSet {S | Q I c S}) :
    Measurable fun S ↦ coinProb (T (slrInput k p S)) (fun c ↦ Q (slrInput k p S) c S) := by
  have h : Measurable fun Sw : (Fin n → EuclideanSpace ℝ (Fin D) × ℝ) ×
      ((Fin n → Fin D → ℤ) × (Fin n → ℤ)) ↦
        coinProb (T (mkI k p Sw.2)) (fun c ↦ Q (mkI k p Sw.2) c Sw.1) := by
    refine measurable_from_prod_countable_left fun w ↦ ?_
    exact measurable_coinProb (T (mkI k p w)) (fun c S ↦ Q (mkI k p w) c S) fun c ↦ hQ _ c
  have h' := h.comp (measurable_id.prodMk (measurable_qS p))
  simp only [slrInput_eq_mkI]
  exact h'

/-- Predicting well is a measurable event of the sample. -/
theorem measurableSet_predictsWell {n D : ℕ} (xs : Fin D → ℝ) (est : Estimate) :
    MeasurableSet {S : Fin n → EuclideanSpace ℝ (Fin D) × ℝ | PredictsWell S xs est} := by
  unfold PredictsWell
  exact measurableSet_le (by fun_prop) measurable_const

/-- The probability over the coins that `A` does not predict well on the regression sample `S`
for the secret `xs`. -/
noncomputable def fail (A : SLRInput × List Bool → Estimate) (e k p : ℕ) {n D : ℕ}
    (xs : Fin D → ℝ) (S : Fin n → EuclideanSpace ℝ (Fin D) × ℝ) : ℝ :=
  coinProb (slrTime e (slrInput k p S)) fun c ↦ ¬ PredictsWell S xs (A (slrInput k p S, c))

/-- The failure probability is measurable in the sample. -/
theorem measurable_fail (A : SLRInput × List Bool → Estimate) (e k p : ℕ) {n D : ℕ}
    (xs : Fin D → ℝ) : Measurable (fail A e k p (n := n) xs) :=
  measurable_coinProb_slr k p (slrTime e) (fun I c S ↦ ¬ PredictsWell S xs (A (I, c)))
    fun _ _ ↦ (measurableSet_predictsWell xs _).compl

/-- **The failure probability of a regression algorithm**, integrated over the sample, is at most
`δ` on a bounded instance. -/
theorem lintegral_fail {A : SLRInput × List Bool → Estimate} {e n D k p : ℕ} {δ : ℝ}
    (h : SolvesSLR A (slrTime e) n D k p δ) {Sg : Matrix (Fin D) (Fin D) ℝ} {xs : Fin D → ℝ}
    (hb : IsBoundedInstance k Sg xs) :
    ∫⁻ S, ENNReal.ofReal (fail A e k p xs S) ∂(Measure.pi fun _ : Fin n ↦ slrLaw Sg xs) ≠ ⊤ ∧
      (∫⁻ S, ENNReal.ofReal (fail A e k p xs S)
        ∂(Measure.pi fun _ : Fin n ↦ slrLaw Sg xs)).toReal ≤ δ := by
  have hs := h Sg xs hb
  have : IsProbabilityMeasure (slrLaw Sg xs) := by
    unfold slrLaw
    infer_instance
  have hsm := measurable_coinProb_slr k p (slrTime e) (n := n)
    (fun I c S ↦ PredictsWell S xs (A (I, c))) fun _ _ ↦ measurableSet_predictsWell xs _
  have hfm := measurable_fail A e k p (n := n) xs
  have hpt : ∀ S : Fin n → EuclideanSpace ℝ (Fin D) × ℝ, ENNReal.ofReal (fail A e k p xs S) +
      ENNReal.ofReal (coinProb (slrTime e (slrInput k p S))
        fun c ↦ PredictsWell S xs (A (slrInput k p S, c))) = 1 := fun S ↦ by
    rw [fail, ← ENNReal.ofReal_add (coinProb_nonneg _ _) (coinProb_nonneg _ _), add_comm,
      coinProb_add_not, ENNReal.ofReal_one]
  have hsum := lintegral_add_left (μ := Measure.pi fun _ : Fin n ↦ slrLaw Sg xs)
    (ENNReal.measurable_ofReal.comp hfm) fun S ↦ ENNReal.ofReal (coinProb (slrTime e
      (slrInput k p S)) fun c ↦ PredictsWell S xs (A (slrInput k p S, c)))
  simp only [Function.comp_apply, hpt, lintegral_const, measure_univ, mul_one] at hsum
  have h1 : ∫⁻ S, ENNReal.ofReal (fail A e k p xs S)
      ∂(Measure.pi fun _ : Fin n ↦ slrLaw Sg xs) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [hsum]; exact le_self_add)
  have h2 : ∫⁻ S, ENNReal.ofReal (coinProb (slrTime e (slrInput k p S))
      fun c ↦ PredictsWell S xs (A (slrInput k p S, c)))
      ∂(Measure.pi fun _ : Fin n ↦ slrLaw Sg xs) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [hsum]; exact le_add_self)
  have ht := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add h1 h2, ENNReal.toReal_one] at ht
  refine ⟨h1, ?_⟩
  unfold slrSuccessProb at hs
  linarith

/-! ### The law of the regression samples -/

/-- The pairing map is measurable. -/
theorem measurable_pairMap (d : ℕ) : Measurable (pairMap d) := by
  refine Measurable.prodMk ?_ ?_
  · refine (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval fun i ↦ ?_)
    by_cases h : (i : ℕ) < d
    · simp only [h, dite_true]
      fun_prop
    · simp only [h, dite_false]
      fun_prop
  · fun_prop

/-- The regression sample of two samples, point by point. -/
noncomputable def pairs {n d : ℕ}
    (zg : (Fin n → EuclideanSpace ℝ (Fin (d + 1))) × (Fin n → EuclideanSpace ℝ (Fin (d + 1)))) :
    Fin n → EuclideanSpace ℝ (Fin (2 * d)) × ℝ :=
  fun i ↦ pairMap d (zg.1 i, zg.2 i)

/-- Pairing two samples is measurable. -/
theorem measurable_pairs (n d : ℕ) : Measurable (pairs (n := n) (d := d)) :=
  Measurable.of_eval fun i ↦ (measurable_pairMap d).comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))

/-- **The regression sample of two independent samples** is a sample of the law of the pairing
of one point of each. -/
theorem map_pairs {n d : ℕ} (μ₁ μ₂ : Measure (EuclideanSpace ℝ (Fin (d + 1))))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    ((Measure.pi fun _ : Fin n ↦ μ₁).prod (Measure.pi fun _ : Fin n ↦ μ₂)).map pairs =
      Measure.pi fun _ : Fin n ↦ (μ₁.prod μ₂).map (pairMap d) := by
  rw [← (measurePreserving_arrowProdEquivProdArrow (EuclideanSpace ℝ (Fin (d + 1)))
    (EuclideanSpace ℝ (Fin (d + 1))) (Fin n) (fun _ ↦ μ₁) (fun _ ↦ μ₂)).map_eq,
    Measure.map_map (measurable_pairs n d) (MeasurableEquiv.measurable _)]
  exact Measure.pi_map_pi (fun _ ↦ (measurable_pairMap d).aemeasurable)

/-- Integrals of functions of the regression sample of two samples. -/
theorem lintegral_pairs {n d : ℕ} (μ₁ μ₂ : Measure (EuclideanSpace ℝ (Fin (d + 1))))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {f : (Fin n → EuclideanSpace ℝ (Fin (2 * d)) × ℝ) → ENNReal} (hf : Measurable f) :
    ∫⁻ zg, f (pairs zg) ∂((Measure.pi fun _ : Fin n ↦ μ₁).prod (Measure.pi fun _ ↦ μ₂)) =
      ∫⁻ S, f S ∂(Measure.pi fun _ : Fin n ↦ (μ₁.prod μ₂).map (pairMap d)) := by
  rw [← map_pairs, lintegral_map hf (measurable_pairs n d)]

/-- Integrals of functions of the regression sample of two samples, in the other order. -/
theorem lintegral_pairs_swap {n d : ℕ} (μ₁ μ₂ : Measure (EuclideanSpace ℝ (Fin (d + 1))))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {f : (Fin n → EuclideanSpace ℝ (Fin (2 * d)) × ℝ) → ENNReal} (hf : Measurable f) :
    ∫⁻ zg, f (pairs zg.swap) ∂((Measure.pi fun _ : Fin n ↦ μ₁).prod (Measure.pi fun _ ↦ μ₂)) =
      ∫⁻ S, f S ∂(Measure.pi fun _ : Fin n ↦ (μ₂.prod μ₁).map (pairMap d)) := by
  rw [← lintegral_pairs μ₂ μ₁ hf]
  exact lintegral_prod_swap (fun zg ↦ f (pairs zg))

/-! ### The precision -/

/-- A frame doubles the length, plus one. -/
theorem length_frame (w : List Bool) : (Encoding.frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => simp [Encoding.frame]
  | cons b w ih =>
    simp only [Encoding.frame, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

/-- The length of an encoded pair. -/
theorem length_encPair {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) (x : α × β) :
    (Encoding.encPair a b x).length = 2 * (a x.1).length + 1 + (b x.2).length := by
  change (Encoding.frame (a x.1) ++ b x.2).length = _
  rw [List.length_append, length_frame]

/-- A natural number in binary is no longer than the number. -/
theorem length_encNat_le (k : ℕ) : (Encoding.encNat k).length ≤ k := by
  change (Nat.bits k).length ≤ k
  rw [Nat.size_eq_bits_len, Nat.size_le]
  exact Nat.lt_two_pow_self

/-- The bound `linB` on the length of the regression inputs is cubic in `n + d + p + 2`. -/
theorem linB_le {n d k p : ℕ} (hk : k ≤ d) :
    linB n (d + 1) k p + 2 ≤ 1000 * (n + d + p + 2) ^ 3 := by
  have h1 := length_encNat_le k
  unfold linB
  have ha : n + 1 ≤ n + d + p + 2 := by omega
  have hb : d + 1 + 1 ≤ n + d + p + 2 := by omega
  have hc : p + n + (d + 1) + 10 ≤ 6 * (n + d + p + 2) := by omega
  have hN : 1 ≤ n + d + p + 2 := by omega
  have h2 : 128 * (n + 1) * (d + 1 + 1) * (p + n + (d + 1) + 10) ≤
      128 * (n + d + p + 2) * (n + d + p + 2) * (6 * (n + d + p + 2)) := by gcongr
  have h3 : (n + d + p + 2) ≤ (n + d + p + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h4 : 1 ≤ (n + d + p + 2) ^ 3 := Nat.one_le_pow _ _ hN
  nlinarith

/-- The exponent of the precision: `(n + d + p + 2)^E0 cA e` bits suffice for the paired test
when the regression algorithm's output is at most `cA` times its running time. -/
def E0 (cA e : ℕ) : ℕ := 4 * cA * 1000 ^ (e + 1) + 13 + 3 * (e + 1)

/-- `p ≤ q` for the precision `q ≥ (n + d + p + 2)^E0`. -/
theorem p_le_q {cA e n d p q : ℕ} (hq : (n + d + p + 2) ^ E0 cA e ≤ q) : p ≤ q := by
  have h1 : n + d + p + 2 ≤ (n + d + p + 2) ^ E0 cA e :=
    Nat.le_self_pow (by unfold E0; omega) _
  omega

/-- **The precision suffices**: for an output of length `H` at most `cA` times the running time
on an input of length `L ≤ linB` with its coins, `2^H · 1024 (d + 1)(R + 1) ≤ 2^q`. -/
theorem prec_le {cA e n d k p q H L : ℕ} (hk : k ≤ d) (hL : L ≤ linB n (d + 1) k p)
    (hH : H ≤ cA * ((L + 2) ^ e + (2 * L + 1 + (L + 2) ^ e) + 1))
    (hq : (n + d + p + 2) ^ E0 cA e ≤ q) :
    2 ^ H * (1024 * (d + 1) * (rad n (d + 1) + 1)) ≤ 2 ^ q := by
  set N := n + d + p + 2 with hNdef
  have hN : 2 ≤ N := by omega
  set B := linB n (d + 1) k p + 2 with hBdef
  have hB1 : 1 ≤ B := by omega
  have hBN : B ≤ 1000 * N ^ 3 := linB_le hk
  have hLB : L + 2 ≤ B := by omega
  -- the output length
  set K := 4 * cA * 1000 ^ (e + 1) with hK
  have hH' : H ≤ K * N ^ (3 * (e + 1)) := by
    have h1 : (L + 2) ^ e ≤ B ^ (e + 1) :=
      (Nat.pow_le_pow_left hLB e).trans (Nat.pow_le_pow_right hB1 (by omega))
    have h2 : 2 * L + 2 ≤ 2 * B ^ (e + 1) := by
      have : B ≤ B ^ (e + 1) := Nat.le_self_pow (by omega) _
      omega
    have h3 : B ^ (e + 1) ≤ 1000 ^ (e + 1) * N ^ (3 * (e + 1)) := by
      rw [pow_mul, ← mul_pow]
      exact Nat.pow_le_pow_left hBN _
    calc H ≤ cA * ((L + 2) ^ e + (2 * L + 1 + (L + 2) ^ e) + 1) := hH
      _ ≤ cA * (4 * B ^ (e + 1)) := by gcongr; omega
      _ ≤ cA * (4 * (1000 ^ (e + 1) * N ^ (3 * (e + 1)))) := by gcongr
      _ = K * N ^ (3 * (e + 1)) := by rw [hK]; ring
  -- the other factor
  have hD : 1024 * (d + 1) * (rad n (d + 1) + 1) ≤ 2 ^ (11 + 2 * N) := by
    have h1 : d + 1 ≤ 2 ^ N := (show d + 1 ≤ N by omega).trans Nat.lt_two_pow_self.le
    have h2 : rad n (d + 1) + 1 ≤ 2 * 2 ^ N := by
      have : rad n (d + 1) + 1 ≤ 2 * N := by unfold rad; omega
      exact this.trans (by have := (Nat.lt_two_pow_self (n := N)).le; omega)
    calc 1024 * (d + 1) * (rad n (d + 1) + 1) ≤ 1024 * 2 ^ N * (2 * 2 ^ N) := by gcongr
      _ = 2 ^ (11 + 2 * N) := by ring
  -- the exponent
  have hE : H + (11 + 2 * N) ≤ q := by
    have hb1 : N ≤ N ^ (3 * (e + 1)) := Nat.le_self_pow (by omega) _
    have h1 : K + 13 ≤ N ^ (K + 13) :=
      Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hN _)
    have h2 : (K + 13) * N ^ (3 * (e + 1)) ≤ N ^ E0 cA e := by
      rw [show E0 cA e = (K + 13) + 3 * (e + 1) by rw [hK]; rfl, pow_add]
      exact Nat.mul_le_mul_right _ h1
    nlinarith
  calc 2 ^ H * (1024 * (d + 1) * (rad n (d + 1) + 1)) ≤ 2 ^ H * 2 ^ (11 + 2 * N) := by gcongr
    _ = 2 ^ (H + (11 + 2 * N)) := (pow_add _ _ _).symm
    _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hE


/-- The output of the regression algorithm on an input of length at most `linB`, with its coins,
is short enough for the precision `q` of the paired test. -/
theorem prec_real {A : SLRInput × List Bool → Estimate} {e cA : ℕ}
    (hcA : ∀ I r, (encEstimate (A (I, r))).length ≤
      cA * (slrTime e I + (Encoding.encPair encSLRInput Encoding.encBits (I, r)).length + 1))
    {n d k p q : ℕ} (hk : k ≤ d) (hq : (n + d + p + 2) ^ E0 cA e ≤ q) {I : SLRInput}
    (hI : (encSLRInput I).length ≤ linB n (d + 1) k p) {c : List Bool}
    (hc : c.length = slrTime e I) :
    (2 : ℝ) ^ (encEstimate (A (I, c))).length *
      (1024 * ((d : ℝ) + 1) * ((rad n (d + 1) : ℝ) + 1)) ≤ 2 ^ q := by
  have h := hcA I c
  rw [length_encPair] at h
  change _ ≤ cA * (slrTime e I + (2 * (encSLRInput I).length + 1 + c.length) + 1) at h
  rw [hc] at h
  exact_mod_cast prec_le hk hI h hq

/-! ### One round, pointwise -/

/-- `1 ≤ rad`. -/
theorem one_le_rad (n m : ℕ) : (1 : ℝ) ≤ (rad n m : ℝ) := by
  unfold rad
  norm_cast
  omega

/-- The coins of a run of the regression algorithm suffice for its running time on a good pair. -/
theorem slrTime_le_lenA {e : ℕ} (δ : ℚ) {n d k p q : ℕ} (hn : 0 < n)
    (ω : Fin n → EuclideanSpace ℝ (Fin (d + 1))) {I : SLRInput}
    (hI : (encSLRInput I).length ≤ linB n (d + 1) k p) :
    slrTime e I ≤ lenA e (spcaInput δ p k q ω) := by
  change ((encSLRInput I).length + 2) ^ e ≤ (linB (nOf (qz q ω)) (mOf (qz q ω)) k p + 2) ^ e
  rw [nOf_qz, mOf_qz q hn]
  exact Nat.pow_le_pow_left (by omega) e

/-- **The first test on a good pair** fails only if the regression algorithm does not predict
well on the regression sample of the pair. -/
theorem fwd_le {A : SLRInput × List Bool → Estimate} {e cA : ℕ}
    (hcA : ∀ I r, (encEstimate (A (I, r))).length ≤
      cA * (slrTime e I + (Encoding.encPair encSLRInput Encoding.encBits (I, r)).length + 1))
    (δ : ℚ) {n d k p q : ℕ} {v : Fin d → SignType} (hn : 0 < n) (hk : k ≤ d)
    (hv : v ∈ spikeSigns d k) (hq : (n + d + p + 2) ^ E0 cA e ≤ q)
    {ω g : Fin n → EuclideanSpace ℝ (Fin (d + 1))} (hG : GoodP n d p q v (ω, g)) :
    coinProb (lenA e (spcaInput δ p k q ω))
        (fun r ↦ pairTest A e k p q (qz q ω) (ownCells n (d + 1) q g) r = false) ≤
      fail A e k p (xsF d v) (pairs (ω, g)) := by
  obtain ⟨hz, hs, hR, hc1, hc2⟩ := hG
  have hpq : p ≤ q := p_le_q hq
  have hI : slrInputOf k p q (qz q ω) (qz q g) = slrInput k p (pairs (ω, g)) :=
    slrInputOf_fwd hpq k hR
  have hlen : (encSLRInput (slrInput k p (pairs (ω, g)))).length ≤ linB n (d + 1) k p := by
    rw [← hI]
    exact length_slrInputOf_le hpq k ω g hz fun i j ↦ (hs i j).1
  rw [ownCells_eq g hs]
  calc coinProb (lenA e (spcaInput δ p k q ω))
        (fun r ↦ pairTest A e k p q (qz q ω) (qz q g) r = false) =
      coinProb (slrTime e (slrInput k p (pairs (ω, g)))) (fun c ↦
        ¬ resid q (predict q (qz q ω) (qz q g) (A (slrInput k p (pairs (ω, g)), c))) (qz q ω) ≤
          resid q (predict q (qz q ω) (qz q g) (A (slrInput k p (pairs (ω, g)), c))) (qz q g)) := by
        rw [← coinProb_take _ _ (slrTime_le_lenA δ hn ω hlen)]
        congr 1
        funext r
        simp only [pairTest, hI, decide_eq_false_iff_not]
    _ ≤ _ := coinProb_mono fun c hc hnot hpw ↦ hnot (test_fwd hv ω g _ q (one_le_rad n (d + 1))
        hz (fun i j ↦ (hs i j).1) hc1 hc2 hpw (prec_real hcA hk hq hlen hc))

/-- **The second test on a good pair** says that the null sample is planted only if the
regression algorithm does not predict well on the regression sample of the swapped pair. -/
theorem bwd_le {A : SLRInput × List Bool → Estimate} {e cA : ℕ}
    (hcA : ∀ I r, (encEstimate (A (I, r))).length ≤
      cA * (slrTime e I + (Encoding.encPair encSLRInput Encoding.encBits (I, r)).length + 1))
    (δ : ℚ) {n d k p q : ℕ} {v : Fin d → SignType} (hn : 0 < n) (hk : k ≤ d)
    (hv : v ∈ spikeSigns d k) (hq : (n + d + p + 2) ^ E0 cA e ≤ q)
    {ω g : Fin n → EuclideanSpace ℝ (Fin (d + 1))} (hG : GoodP n d p q v (ω, g)) :
    coinProb (lenA e (spcaInput δ p k q ω))
        (fun r ↦ pairTest A e k p q (ownCells n (d + 1) q g) (qz q ω) r = true) ≤
      fail A e k p (xsB d v) (pairs (ω, g).swap) := by
  obtain ⟨hz, hs, hR, hc1, hc2⟩ := hG
  have hpq : p ≤ q := p_le_q hq
  have hI : slrInputOf k p q (qz q g) (qz q ω) = slrInput k p (pairs (ω, g).swap) :=
    slrInputOf_bwd hpq k hR
  have hlen : (encSLRInput (slrInput k p (pairs (ω, g).swap))).length ≤
      linB n (d + 1) k p := by
    rw [← hI]
    exact length_slrInputOf_le hpq k g ω (fun i j ↦ (hs i j).1) hz
  rw [ownCells_eq g hs]
  calc coinProb (lenA e (spcaInput δ p k q ω))
        (fun r ↦ pairTest A e k p q (qz q g) (qz q ω) r = true) =
      coinProb (slrTime e (slrInput k p (pairs (ω, g).swap))) (fun c ↦
        resid q (predict q (qz q g) (qz q ω) (A (slrInput k p (pairs (ω, g).swap), c))) (qz q g) ≤
          resid q (predict q (qz q g) (qz q ω) (A (slrInput k p (pairs (ω, g).swap), c)))
            (qz q ω)) := by
        rw [← coinProb_take _ _ (slrTime_le_lenA δ hn ω hlen)]
        congr 1
        funext r
        simp only [pairTest, hI, decide_eq_true_eq]
    _ ≤ _ := coinProb_mono fun c hc hle hpw ↦ (test_bwd hn hv ω g _ q (one_le_rad n (d + 1))
        hz (fun i j ↦ (hs i j).1) hc1 hc2 hpw (prec_real hcA hk hq hlen hc)) hle

/-- The first test on any pair, with the bad pairs in `B`. -/
theorem fwd_le_ind {A : SLRInput × List Bool → Estimate} {e cA : ℕ}
    (hcA : ∀ I r, (encEstimate (A (I, r))).length ≤
      cA * (slrTime e I + (Encoding.encPair encSLRInput Encoding.encBits (I, r)).length + 1))
    (δ : ℚ) {n d k p q : ℕ} {v : Fin d → SignType} (hn : 0 < n) (hk : k ≤ d)
    (hv : v ∈ spikeSigns d k) (hq : (n + d + p + 2) ^ E0 cA e ≤ q)
    {B : Set ((Fin n → EuclideanSpace ℝ (Fin (d + 1))) × (Fin n → EuclideanSpace ℝ (Fin (d + 1))))}
    (hB : {zg | ¬ GoodP n d p q v zg} ⊆ B) (ω g : Fin n → EuclideanSpace ℝ (Fin (d + 1))) :
    ENNReal.ofReal (coinProb (lenA e (spcaInput δ p k q ω))
        (fun r ↦ pairTest A e k p q (qz q ω) (ownCells n (d + 1) q g) r = false)) ≤
      ENNReal.ofReal (fail A e k p (xsF d v) (pairs (ω, g))) + B.indicator 1 (ω, g) := by
  by_cases hG : GoodP n d p q v (ω, g)
  · exact (ENNReal.ofReal_le_ofReal (fwd_le hcA δ hn hk hv hq hG)).trans le_self_add
  · rw [Set.indicator_of_mem (hB hG), Pi.one_apply]
    exact (ENNReal.ofReal_le_one.2 (coinProb_le_one _ _)).trans le_add_self

/-- The second test on any pair, with the bad pairs in `B`. -/
theorem bwd_le_ind {A : SLRInput × List Bool → Estimate} {e cA : ℕ}
    (hcA : ∀ I r, (encEstimate (A (I, r))).length ≤
      cA * (slrTime e I + (Encoding.encPair encSLRInput Encoding.encBits (I, r)).length + 1))
    (δ : ℚ) {n d k p q : ℕ} {v : Fin d → SignType} (hn : 0 < n) (hk : k ≤ d)
    (hv : v ∈ spikeSigns d k) (hq : (n + d + p + 2) ^ E0 cA e ≤ q)
    {B : Set ((Fin n → EuclideanSpace ℝ (Fin (d + 1))) × (Fin n → EuclideanSpace ℝ (Fin (d + 1))))}
    (hB : {zg | ¬ GoodP n d p q v zg} ⊆ B) (ω g : Fin n → EuclideanSpace ℝ (Fin (d + 1))) :
    ENNReal.ofReal (coinProb (lenA e (spcaInput δ p k q ω))
        (fun r ↦ pairTest A e k p q (ownCells n (d + 1) q g) (qz q ω) r = true)) ≤
      ENNReal.ofReal (fail A e k p (xsB d v) (pairs (ω, g).swap)) + B.indicator 1 (ω, g) := by
  by_cases hG : GoodP n d p q v (ω, g)
  · exact (ENNReal.ofReal_le_ofReal (bwd_le hcA δ hn hk hv hq hG)).trans le_self_add
  · rw [Set.indicator_of_mem (hB hG), Pi.one_apply]
    exact (ENNReal.ofReal_le_one.2 (coinProb_le_one _ _)).trans le_add_self

/-! ### Integration -/

/-- The integral of a nonnegative function is at most its lower integral. -/
theorem ofReal_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ}
    (hf : ∀ a, 0 ≤ f a) : ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
  by_cases hi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)]
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact zero_le

/-- **A round on planted input**, with the bad pairs in a measurable set `B`: its failure
probability, integrated over the input, is at most the failure probabilities of the regression
algorithm on the two regression instances plus twice the probability of `B`. -/
theorem round_le {A : SLRInput × List Bool → Estimate} {e cA : ℕ}
    (hcA : ∀ I r, (encEstimate (A (I, r))).length ≤
      cA * (slrTime e I + (Encoding.encPair encSLRInput Encoding.encBits (I, r)).length + 1))
    (δ : ℚ) {n d k p q : ℕ} {v : Fin d → SignType} (hn : 0 < n) (hk : k ≤ d)
    (hv : v ∈ spikeSigns d k) (hq : (n + d + p + 2) ^ E0 cA e ≤ q)
    {B : Set ((Fin n → EuclideanSpace ℝ (Fin (d + 1))) × (Fin n → EuclideanSpace ℝ (Fin (d + 1))))}
    (hBm : MeasurableSet B) (hB : {zg | ¬ GoodP n d p q v zg} ⊆ B) :
    ∫⁻ ω, ENNReal.ofReal (coinProb (lenBlk e (spcaInput δ p k q ω))
          fun b ↦ blockTest A e (spcaInput δ p k q ω) b = false)
        ∂(Measure.pi fun _ : Fin n ↦ plantedLaw d k v) ≤
      (∫⁻ S, ENNReal.ofReal (fail A e k p (xsF d v) S)
          ∂(Measure.pi fun _ : Fin n ↦ slrLaw (covF d k v) (xsF d v)) +
        (Measure.pi fun _ : Fin n ↦ plantedLaw d k v).prod (gRows n (d + 1)) B) +
      (∫⁻ S, ENNReal.ofReal (fail A e k p (xsB d v) S)
          ∂(Measure.pi fun _ : Fin n ↦ slrLaw (covB d k v) (xsB d v)) +
        (Measure.pi fun _ : Fin n ↦ plantedLaw d k v).prod (gRows n (d + 1)) B) := by
  have hfF : Measurable fun zg : (Fin n → EuclideanSpace ℝ (Fin (d + 1))) ×
      (Fin n → EuclideanSpace ℝ (Fin (d + 1))) ↦
        ENNReal.ofReal (fail A e k p (xsF d v) (pairs zg)) :=
    ENNReal.measurable_ofReal.comp ((measurable_fail A e k p _).comp (measurable_pairs n d))
  have hfB : Measurable fun zg : (Fin n → EuclideanSpace ℝ (Fin (d + 1))) ×
      (Fin n → EuclideanSpace ℝ (Fin (d + 1))) ↦
        ENNReal.ofReal (fail A e k p (xsB d v) (pairs zg.swap)) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_fail A e k p _).comp ((measurable_pairs n d).comp measurable_swap))
  have hHF : Measurable fun zg ↦ ENNReal.ofReal (fail A e k p (xsF d v) (pairs zg)) +
      B.indicator 1 zg := hfF.add (measurable_one.indicator hBm)
  have hHB : Measurable fun zg ↦ ENNReal.ofReal (fail A e k p (xsB d v) (pairs zg.swap)) +
      B.indicator 1 zg := hfB.add (measurable_one.indicator hBm)
  -- pointwise in the input
  have hpt : ∀ ω : Fin n → EuclideanSpace ℝ (Fin (d + 1)),
      ENNReal.ofReal (coinProb (lenBlk e (spcaInput δ p k q ω))
          fun b ↦ blockTest A e (spcaInput δ p k q ω) b = false) ≤
        ∫⁻ g, (ENNReal.ofReal (fail A e k p (xsF d v) (pairs (ω, g))) + B.indicator 1 (ω, g))
          ∂(gRows n (d + 1)) +
        ∫⁻ g, (ENNReal.ofReal (fail A e k p (xsB d v) (pairs (ω, g).swap)) +
          B.indicator 1 (ω, g)) ∂(gRows n (d + 1)) := by
    intro ω
    have hnx : nOf (spcaInput δ p k q ω).points = n := nOf_qz q ω
    have hmx : mOf (spcaInput δ p k q ω).points = d + 1 := mOf_qz q hn ω
    have h1 := coinProb_blockTest_false_le A e (spcaInput δ p k q ω)
    rw [coinProb_fwd_false A e _ hnx hmx, coinProb_bwd_true A e _ hnx hmx] at h1
    refine (ENNReal.ofReal_le_ofReal h1).trans (ENNReal.ofReal_add_le.trans (add_le_add ?_ ?_))
    · refine (ofReal_integral_le _ fun g ↦ coinProb_nonneg _ _).trans
        (lintegral_mono fun g ↦ ?_)
      exact fwd_le_ind hcA δ hn hk hv hq hB ω g
    · refine (ofReal_integral_le _ fun g ↦ coinProb_nonneg _ _).trans
        (lintegral_mono fun g ↦ ?_)
      exact bwd_le_ind hcA δ hn hk hv hq hB ω g
  -- integrate
  have hf1 : Measurable fun S : Fin n → EuclideanSpace ℝ (Fin (2 * d)) × ℝ ↦
      ENNReal.ofReal (fail A e k p (xsF d v) S) :=
    ENNReal.measurable_ofReal.comp (measurable_fail A e k p (xsF d v))
  have hf2 : Measurable fun S : Fin n → EuclideanSpace ℝ (Fin (2 * d)) × ℝ ↦
      ENNReal.ofReal (fail A e k p (xsB d v) S) :=
    ENNReal.measurable_ofReal.comp (measurable_fail A e k p (xsB d v))
  have hint := lintegral_mono (μ := Measure.pi fun _ : Fin n ↦ plantedLaw d k v) hpt
  rw [lintegral_add_left (hHF.lintegral_prod_right' (ν := gRows n (d + 1))),
    ← lintegral_prod _ hHF.aemeasurable, ← lintegral_prod _ hHB.aemeasurable,
    lintegral_add_left hfF, lintegral_add_left hfB, lintegral_indicator_one hBm,
    lintegral_pairs (plantedLaw d k v) (nullLaw (d + 1)) hf1,
    lintegral_pairs_swap (plantedLaw d k v) (nullLaw (d + 1)) hf2,
    pairMap_fwd hv, pairMap_bwd hv] at hint
  exact hint

end BDT24.Analysis.PL

namespace BDT24.Analysis

open MeasureTheory ProbabilityTheory BDT24.Alg BDT24.Prob

/-- **The algorithm fails only if a round fails.** -/
theorem output_false_le {A : SLRInput × List Bool → Estimate} {e : ℕ} (T : SPCAInput → ℕ)
    (hT : ∀ x, rounds x.δ (nOf x.points) * lenBlk e x ≤ T x) (δ : ℚ) (p k q n : ℕ) {m : ℕ}
    (S : Matrix (Fin m) (Fin m) ℝ) :
    spcaOutputProb (algB A e) T δ p k q n S false ≤ rounds δ n *
      (∫⁻ ω, ENNReal.ofReal (coinProb (lenBlk e (spcaInput δ p k q ω))
          fun b ↦ blockTest A e (spcaInput δ p k q ω) b = false)
        ∂(Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 S)).toReal := by
  have hpt : ∀ ω : Fin n → EuclideanSpace ℝ (Fin m),
      coinProb (T (spcaInput δ p k q ω)) (fun c ↦ algB A e (spcaInput δ p k q ω, c) = false) ≤
        rounds δ n * coinProb (lenBlk e (spcaInput δ p k q ω))
          (fun b ↦ blockTest A e (spcaInput δ p k q ω) b = false) := by
    intro ω
    have hx : rounds (spcaInput δ p k q ω).δ (nOf (spcaInput δ p k q ω).points) = rounds δ n := by
      rw [spcaInput_points, nOf_qz]
      rfl
    have h1 := coinProb_add_not (T (spcaInput δ p k q ω))
      (fun c ↦ algB A e (spcaInput δ p k q ω, c) = true)
    have h2 := coinProb_add_not (lenBlk e (spcaInput δ p k q ω))
      (fun b ↦ blockTest A e (spcaInput δ p k q ω) b = true)
    simp only [Bool.not_eq_true] at h1 h2
    rw [coinProb_algB_true A e _ _ (hT _), hx] at h1
    have hP0 := PL.coinProb_nonneg (lenBlk e (spcaInput δ p k q ω))
      (fun b ↦ blockTest A e (spcaInput δ p k q ω) b = true)
    have hP1 := PL.coinProb_le_one (lenBlk e (spcaInput δ p k q ω))
      (fun b ↦ blockTest A e (spcaInput δ p k q ω) b = true)
    generalize coinProb (lenBlk e (spcaInput δ p k q ω))
      (fun b ↦ blockTest A e (spcaInput δ p k q ω) b = true) = P at h1 h2 hP0 hP1
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ P - 1 by linarith) (rounds δ n)
    rw [add_sub_cancel] at hb
    have hcb : coinProb (lenBlk e (spcaInput δ p k q ω))
        (fun b ↦ blockTest A e (spcaInput δ p k q ω) b = false) = 1 - P := by linarith
    rw [hcb]
    linarith
  have hfin : ∫⁻ ω, ENNReal.ofReal (coinProb (lenBlk e (spcaInput δ p k q ω))
      fun b ↦ blockTest A e (spcaInput δ p k q ω) b = false)
        ∂(Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 S) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂(Measure.pi fun _ : Fin n ↦
      multivariateGaussian 0 S)) (by simp) (lintegral_mono fun ω ↦ ?_)
    exact ENNReal.ofReal_le_one.2 (PL.coinProb_le_one _ _)
  unfold spcaOutputProb
  calc (∫⁻ ω, ENNReal.ofReal (coinProb (T (spcaInput δ p k q ω))
          fun c ↦ algB A e (spcaInput δ p k q ω, c) = false)
        ∂(Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 S)).toReal
      ≤ (ENNReal.ofReal (rounds δ n) * ∫⁻ ω, ENNReal.ofReal (coinProb
          (lenBlk e (spcaInput δ p k q ω)) fun b ↦ blockTest A e (spcaInput δ p k q ω) b = false)
        ∂(Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 S)).toReal := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine ENNReal.toReal_mono ?_ (lintegral_mono fun ω ↦ ?_)
        · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
        · rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Nat.cast_nonneg _)]

/-- **A round on planted input fails with probability at most `2 (δ + P(not good))`.** -/
theorem planted_calls {A : SLRInput × List Bool → Estimate} {e : ℕ}
    (hA : RunsInTime encSLRInput encEstimate A (slrTime e)) :
    ∃ E₀ : ℕ, ∀ (δ : ℚ) (n d k p q : ℕ) (v : Fin d → SignType), 0 < n → k ≤ d →
      v ∈ spikeSigns d k → SolvesSLR A (slrTime e) n (2 * d) k p δ →
      (n + d + p + 2) ^ E₀ ≤ q →
      (∫⁻ ω, ENNReal.ofReal (coinProb (lenBlk e (spcaInput δ p k q ω))
          fun b ↦ blockTest A e (spcaInput δ p k q ω) b = false)
        ∂(Measure.pi fun _ : Fin n ↦ plantedLaw d k v)).toReal ≤
      2 * (δ + ((Measure.pi fun _ : Fin n ↦ plantedLaw d k v).prod (gRows n (d + 1))).real
        {zg | ¬ GoodP n d p q v zg}) := by
  obtain ⟨cA, hcA⟩ := output_length_le hA
  refine ⟨PL.E0 cA e, fun δ n d k p q v hn hk hv hS hq ↦ ?_⟩
  have h := PL.round_le hcA δ hn hk hv hq (measurableSet_toMeasurable _ _)
    (subset_toMeasurable ((Measure.pi fun _ : Fin n ↦ plantedLaw d k v).prod (gRows n (d + 1)))
      {zg | ¬ GoodP n d p q v zg})
  rw [measure_toMeasurable] at h
  obtain ⟨hF1, hF2⟩ := PL.lintegral_fail hS (bounded_fwd hv)
  obtain ⟨hB1, hB2⟩ := PL.lintegral_fail hS (bounded_bwd hv)
  have hbad : (Measure.pi fun _ : Fin n ↦ plantedLaw d k v).prod (gRows n (d + 1))
      {zg | ¬ GoodP n d p q v zg} ≠ ⊤ := measure_ne_top _ _
  refine (ENNReal.toReal_mono (by simp [hF1, hB1, hbad]) h).trans ?_
  rw [ENNReal.toReal_add (by simp [hF1, hbad]) (by simp [hB1, hbad]),
    ENNReal.toReal_add hF1 hbad, ENNReal.toReal_add hB1 hbad, ← measureReal_def]
  linarith

end BDT24.Analysis
