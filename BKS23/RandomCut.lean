module

public import BKS23.Random
public import BKS23.Certificate
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# The cut of a random graph

[BKS23, `lem:balacedness-density-half`, `lem:balacedness-density-large-p`]: with high probability
the cut of `G(V, p)` between a set `U` and its complement has the two properties the biclique
certificates need (`BKS23.Biclique.Axioms.certificate_pBiased`).

* **Balancedness** (`BKS23.Random.Balanced`): for `S ≠ T ⊆ U` of size `m ≤ t`, the sum
  `∑_{v ∉ U} u_S(v) u_T(v)` of products of `p`-biased characters is at most
  `Δ_m = M^m √(2 |V| log(t |U|^(2m) / δ))`, with `M = max((1-p)/p, p/(1-p))`
  (`BKS23.Random.prob_not_balanced`).
* **Bounded degrees** (`BKS23.Random.DegreeLE`): every `v ∉ U` has at most
  `|U| p + √(2 |U| log(|V| / δ))` neighbours in `U` (`BKS23.Random.prob_not_degreeLE`).

Both fail with probability at most `δ`. The proofs are Hoeffding's inequality
(`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`, with Hoeffding's lemma) and union bounds, on
the law of the cut (`BKS23.Random.map_cut_binomialRandom`): the terms of the sums over `v ∉ U`
are functions of independent blocks of coins, and those over `w ∈ U` of independent coins. The
products `u_S(v) u_T(v)` have mean zero because `S ≠ T` and the characters have mean zero.

The bounds on `Δ` are the paper's up to constants: Hoeffding gives `√(2 |V| log(…))` per pair,
times the range `M^m` of the products. That range is the paper's `(p/(1-p))^r` for `p ≥ 1/2`; for
`p < 1/2` it is `((1-p)/p)^m`, which is why the paper reduces `p ≤ 1/2` to `p = 1/2`
(`BKS23/README.md`, item 4; here `BKS23.Random.prob_not_le_good_half`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval SimpleGraph Finset Real

namespace BKS23.Random

/-! ### Hoeffding's inequality for bounded centred variables -/

/-- **Hoeffding's inequality** for independent centred variables bounded by `B`:
`P(∑ Xᵢ ≥ ε) ≤ exp(-ε² / (2 n B²))`. -/
theorem hoeffding {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (h : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i ω, |X i ω| ≤ B) (hc : ∀ i, μ[X i] = 0) (s : Finset ι) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤ exp (-ε ^ 2 / (2 * (s.card * B ^ 2))) := by
  have hsub : ∀ i ∈ s, HasSubgaussianMGF (X i) ((‖B - (-B)‖₊ / 2) ^ 2) μ := fun i _ ↦
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hm i).aemeasurable
      (ae_of_all _ fun ω ↦ abs_le.1 (hb i ω)) (hc i)
  refine (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h hsub hε).trans_eq ?_
  have hc : ((∑ _i ∈ s, (‖B - (-B)‖₊ / 2) ^ 2 : NNReal) : ℝ) = s.card * B ^ 2 := by
    rw [sum_const, nsmul_eq_mul]
    push_cast
    rw [Real.norm_eq_abs, sub_neg_eq_add, abs_of_nonneg (by linarith)]
    ring
  rw [hc]

/-! ### Characters of coins -/

theorem charP_eq_chi {V : Type*} {p : ℝ} {adj : V → V → Prop} [DecidableRel adj] (w v : V) :
    Biclique.charP p adj w v = chi p (adj w v) := by
  unfold Biclique.charP chi
  by_cases h : adj w v <;> simp [h]

theorem abs_chi_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (b : Prop) :
    |chi p b| ≤ √(Biclique.charMax p) := by
  classical
  have h := Biclique.charP_sq_le (adj := fun (_ _ : Unit) ↦ b) hp hp1 () ()
  rw [charP_eq_chi] at h
  exact Real.abs_le_sqrt h

/-! ### Characters of sets in a block -/

variable {V : Type*} [DecidableEq V] (U : Finset V)

theorem charSet_eq_blockChar {p : ℝ} (R : SimpleGraph V) [DecidableRel R.Adj] {S : Finset V}
    (hS : S ⊆ U) {v : V} (hv : v ∉ U) :
    Biclique.charSet p R.Adj S v = blockChar U p S (cut U R ⟨v, hv⟩) := by
  rw [Biclique.charSet, blockChar]
  calc ∏ w ∈ S, Biclique.charP p R.Adj w v = ∏ w ∈ S, chi p (R.Adj w v) :=
        prod_congr rfl fun w _ ↦ charP_eq_chi w v
    _ = ∏ w ∈ S.subtype (· ∈ U), chi p (R.Adj w v) := (prod_subtype_of_mem _ hS).symm
    _ = _ := rfl

theorem abs_blockChar_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {S : Finset V} (hS : S ⊆ U)
    (x : {w // w ∈ U} → Prop) : |blockChar U p S x| ≤ √(Biclique.charMax p) ^ S.card := by
  rw [blockChar, abs_prod, ← card_subtype_of_subset U hS, ← prod_const]
  exact prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun w _ ↦ abs_chi_le hp hp1 _

/-! ### Balancedness -/

variable [Fintype V]

theorem card_out : Fintype.card {v // v ∉ U} = Uᶜ.card := by
  classical
  rw [Fintype.card_subtype]
  congr 1
  ext v
  simp

/-- **Hoeffding for one pair.** Under the law of the cut, `∑_v u_S(v) u_T(v) ≥ ε` with
probability at most `exp(-ε² / (2 |V| M^(2|S|)))`. -/
theorem cutLaw_pair_le {p : I} (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {S T : Finset V}
    (hS : S ⊆ U) (hT : T ⊆ U) (hST : S ≠ T) (hcard : S.card = T.card) {ε : ℝ} (hε : 0 ≤ ε) :
    (cutLaw V U p).real {ω | ε ≤ ∑ v, blockChar U p S (ω v) * blockChar U p T (ω v)} ≤
      exp (-ε ^ 2 / (2 * (Uᶜ.card * (Biclique.charMax p ^ S.card) ^ 2))) := by
  set Y : ({w // w ∈ U} → Prop) → ℝ := fun x ↦ blockChar U p S x * blockChar U p T x
  have hY : Measurable Y := Measurable.of_discrete
  have hM := Biclique.one_le_charMax hp hp1
  have hb : ∀ x, |Y x| ≤ Biclique.charMax p ^ S.card := by
    intro x
    rw [abs_mul]
    calc |blockChar U p S x| * |blockChar U p T x|
        ≤ √(Biclique.charMax p) ^ S.card * √(Biclique.charMax p) ^ S.card :=
          mul_le_mul (abs_blockChar_le U hp hp1 hS x)
            (hcard ▸ abs_blockChar_le U hp hp1 hT x) (abs_nonneg _) (by positivity)
      _ = Biclique.charMax p ^ S.card := by
          rw [← mul_pow, Real.mul_self_sqrt (by linarith)]
  have hind : iIndepFun (fun v ω ↦ Y (ω v)) (cutLaw V U p) := by
    rw [cutLaw_eq]
    exact iIndepFun_infinitePi (P := fun _ ↦ blockLaw V U p) (X := fun _ ↦ Y) (fun _ ↦ hY)
  have h := hoeffding (μ := cutLaw V U p) (X := fun v ω ↦ Y (ω v)) hind
    (fun v ↦ hY.comp (measurable_pi_apply v)) (by positivity) (fun v ω ↦ hb (ω v))
    (fun v ↦ by
      rw [cutLaw_eq, ← integral_map (measurable_pi_apply v).aemeasurable
        hY.aestronglyMeasurable, Measure.infinitePi_map_eval]
      exact integral_blockChar_mul U hp hp1 hS hST hcard) univ hε
  rwa [card_univ, card_out] at h

open Classical in
/-- The cut of `R` between `U` and its complement is balanced at levels `1, …, t` with bounds
`Δ`, for `p`-biased characters: the hypothesis `hbal` of
`BKS23.Biclique.Axioms.certificate_pBiased`. -/
def Balanced (p : ℝ) (t : ℕ) (Δ : ℕ → ℝ) (R : SimpleGraph V) : Prop :=
  ∀ m ∈ Icc 1 t, ∀ S ∈ U.powersetCard m, ∀ T ∈ U.powersetCard m, S ≠ T →
    ∑ v ∈ Uᶜ, Biclique.charSet p R.Adj S v * Biclique.charSet p R.Adj T v ≤ Δ m

/-- The balancedness bound `Δ_m = M^m √(2 |V| log(t |U|^(2m) / δ))`. -/
noncomputable def balance (p δ : ℝ) (t m : ℕ) : ℝ :=
  Biclique.charMax p ^ m * √(2 * Uᶜ.card * Real.log (t * U.card ^ (2 * m) / δ))

open Classical in
/-- One pair, on the graph. -/
theorem prob_pair_le {p : I} (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {S T : Finset V}
    (hS : S ⊆ U) (hT : T ⊆ U) (hST : S ≠ T) (hcard : S.card = T.card) {ε : ℝ} (hε : 0 ≤ ε) :
    (G(V, p)).real {R | ε ≤ ∑ v ∈ Uᶜ, Biclique.charSet p R.Adj S v *
        Biclique.charSet p R.Adj T v} ≤
      exp (-ε ^ 2 / (2 * (Uᶜ.card * (Biclique.charMax p ^ S.card) ^ 2))) := by
  have hset : {R : SimpleGraph V | ε ≤ ∑ v ∈ Uᶜ, Biclique.charSet p R.Adj S v *
      Biclique.charSet p R.Adj T v} = cut U ⁻¹'
        {ω | ε ≤ ∑ v, blockChar U p S (ω v) * blockChar U p T (ω v)} := by
    ext R
    change (ε ≤ _) ↔ (ε ≤ _)
    rw [sum_subtype Uᶜ (p := (· ∉ U)) (fun v ↦ mem_compl)]
    refine iff_of_eq (congrArg _ (sum_congr rfl fun v _ ↦ ?_))
    rw [charSet_eq_blockChar U R hS v.2, charSet_eq_blockChar U R hT v.2]
  rw [hset, measureReal_def, binomialRandom_cut_preimage U p MeasurableSet.of_discrete,
    ← measureReal_def]
  exact cutLaw_pair_le U hp hp1 hS hT hST hcard hε

/-- **Balancedness** [BKS23, `lem:balacedness-density-half`, `lem:balacedness-density-large-p`]:
the cut of `G(V, p)` fails to be balanced with the bounds `balance` with probability at most `δ`.
A union bound over the levels `m ≤ t` and the at most `|U|^(2m)` pairs at level `m`, each failing
with probability at most `δ / (t |U|^(2m))`. -/
theorem prob_not_balanced {p : I} (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (t : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (G(V, p)).real {R | ¬ Balanced U p t (balance U p δ t) R} ≤ δ := by
  classical
  -- Degenerate cases: no pairs or no outside vertices.
  rcases Nat.eq_zero_or_pos Uᶜ.card with hV | hV
  · have : {R : SimpleGraph V | ¬ Balanced U p t (balance U p δ t) R} = ∅ := by
      ext R
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro m _ S _ T _ _
      rw [card_eq_zero.1 hV, sum_empty]
      exact mul_nonneg (pow_nonneg (by linarith [Biclique.one_le_charMax hp hp1]) _)
        (Real.sqrt_nonneg _)
    rw [this, measureReal_empty]
    exact hδ.le
  set M := Biclique.charMax p
  have hM : 1 ≤ M := Biclique.one_le_charMax hp hp1
  -- Each pair fails with probability at most `δ / (t |U|^(2m))`.
  have hterm : ∀ m ∈ Icc 1 t, ∀ S ∈ U.powersetCard m, ∀ T ∈ U.powersetCard m, S ≠ T →
      (G(V, p)).real {R | balance U p δ t m ≤ ∑ v ∈ Uᶜ, Biclique.charSet p R.Adj S v *
        Biclique.charSet p R.Adj T v} ≤ δ / (t * U.card ^ (2 * m)) := by
    intro m hm S hS T hT hST
    rw [mem_powersetCard] at hS hT
    rw [mem_Icc] at hm
    have hU : 1 ≤ U.card := by
      have := card_le_card hS.1
      omega
    have hx : 1 ≤ (t : ℝ) * U.card ^ (2 * m) / δ := by
      rw [le_div_iff₀ hδ, one_mul]
      have ht : (1 : ℝ) ≤ t := by exact_mod_cast hm.1.trans hm.2
      have hUm : (1 : ℝ) ≤ (U.card : ℝ) ^ (2 * m) := one_le_pow₀ (by exact_mod_cast hU)
      nlinarith
    have hL : 0 ≤ Real.log ((t : ℝ) * U.card ^ (2 * m) / δ) := Real.log_nonneg hx
    refine (prob_pair_le U hp hp1 hS.1 hT.1 hST (hS.2.trans hT.2.symm) (by
      unfold balance; positivity)).trans (le_of_eq ?_)
    rw [hS.2, balance, mul_pow, Real.sq_sqrt (by positivity)]
    have hV' : (0 : ℝ) < Uᶜ.card := by exact_mod_cast hV
    have hMm : (0 : ℝ) < M ^ m := by positivity
    rw [show -((M ^ m) ^ 2 * (2 * Uᶜ.card * Real.log ((t : ℝ) * U.card ^ (2 * m) / δ))) /
        (2 * (Uᶜ.card * (M ^ m) ^ 2)) = -Real.log ((t : ℝ) * U.card ^ (2 * m) / δ) by
      field_simp]
    rw [Real.exp_neg, Real.exp_log (by linarith), inv_div]
  -- The union bound.
  have hsub : {R : SimpleGraph V | ¬ Balanced U p t (balance U p δ t) R} ⊆
      ⋃ m ∈ Icc 1 t, ⋃ S ∈ U.powersetCard m, ⋃ T ∈ (U.powersetCard m).erase S,
        {R | balance U p δ t m ≤ ∑ v ∈ Uᶜ, Biclique.charSet p R.Adj S v *
          Biclique.charSet p R.Adj T v} := by
    intro R hR
    simp only [Balanced, Set.mem_ofPred_eq, not_forall, not_le] at hR
    obtain ⟨m, hm, S, hS, T, hT, hST, hlt⟩ := hR
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, mem_erase]
    exact ⟨m, hm, S, hS, T, ⟨Ne.symm hST, hT⟩, hlt.le⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc ∑ m ∈ Icc 1 t, (G(V, p)).real (⋃ S ∈ U.powersetCard m, ⋃ T ∈ (U.powersetCard m).erase S,
        {R | balance U p δ t m ≤ ∑ v ∈ Uᶜ, Biclique.charSet p R.Adj S v *
          Biclique.charSet p R.Adj T v})
      ≤ ∑ _m ∈ Icc 1 t, δ / t := by
        refine sum_le_sum fun m hm ↦ ?_
        refine (measureReal_biUnion_finset_le _ _).trans ?_
        refine (sum_le_sum fun S hS ↦ measureReal_biUnion_finset_le _ _).trans ?_
        have hpairs : ∑ S ∈ U.powersetCard m, ∑ T ∈ (U.powersetCard m).erase S,
            (G(V, p)).real {R | balance U p δ t m ≤ ∑ v ∈ Uᶜ, Biclique.charSet p R.Adj S v *
              Biclique.charSet p R.Adj T v} ≤
            ∑ _S ∈ U.powersetCard m, ∑ _T ∈ U.powersetCard m, δ / (t * U.card ^ (2 * m)) := by
          refine sum_le_sum fun S hS ↦ ?_
          refine (sum_le_sum fun T hT ↦ hterm m hm S hS T (mem_of_mem_erase hT)
            (ne_of_mem_erase hT).symm).trans ?_
          exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ ↦ by positivity
        refine hpairs.trans ?_
        rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, card_powersetCard]
        rcases Nat.eq_zero_or_pos (U.card.choose m) with h0 | hpos
        · rw [h0]
          simp only [Nat.cast_zero, zero_mul]
          positivity
        have hU : 1 ≤ U.card := by
          by_contra h
          have : U.card = 0 := by omega
          rw [this, Nat.choose_eq_zero_of_lt (by have := (mem_Icc.1 hm).1; omega)] at hpos
          exact lt_irrefl _ hpos
        have hc : ((U.card.choose m : ℕ) : ℝ) ≤ (U.card : ℝ) ^ m := by
          exact_mod_cast Nat.choose_le_pow _ _
        have ht : (0 : ℝ) < t := by
          have := (mem_Icc.1 hm).1.trans (mem_Icc.1 hm).2
          exact_mod_cast this
        have hUm : (0 : ℝ) < (U.card : ℝ) ^ (2 * m) := by
          have : (0 : ℝ) < U.card := by exact_mod_cast hU
          positivity
        calc ((U.card.choose m : ℕ) : ℝ) * (((U.card.choose m : ℕ) : ℝ) *
              (δ / (t * U.card ^ (2 * m))))
            ≤ (U.card : ℝ) ^ m * ((U.card : ℝ) ^ m * (δ / (t * U.card ^ (2 * m)))) := by
              gcongr
          _ = δ / t := by
              rw [pow_mul, show (U.card : ℝ) ^ 2 = U.card * U.card by ring, mul_pow]
              field_simp
    _ ≤ δ := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        rcases Nat.eq_zero_or_pos t with rfl | ht
        · simp only [Nat.cast_zero, zero_mul]
          exact hδ.le
        · have : (0 : ℝ) < t := by exact_mod_cast ht
          exact (by field_simp : (t : ℝ) * (δ / t) = δ).le

/-! ### Degrees -/

open Classical in
/-- Every vertex outside `U` has at most `d` neighbours in `U`: the hypothesis `hd` of
`BKS23.Biclique.Axioms.certificate_pBiased`. -/
def DegreeLE (d : ℝ) (R : SimpleGraph V) : Prop :=
  ∀ v ∈ Uᶜ, ((U.filter (R.Adj · v)).card : ℝ) ≤ d

/-- The degree bound `|U| p + √(2 |U| log(|V| / δ))`. -/
noncomputable def degreeBound (p δ : ℝ) : ℝ :=
  U.card * p + √(2 * U.card * Real.log (Uᶜ.card / δ))

/-- A coin centred: `1 - p` for heads, `-p` for tails. -/
noncomputable def centred (p : ℝ) (b : Prop) : ℝ := by
  classical
  exact (if b then 1 else 0) - p

theorem integral_centred (p : I) : ∫ b, centred p b ∂Ber(True, False, p) = 0 := by
  rw [integral_bernoulliMeasure]
  simp only [centred, ite_true, ite_false, smul_eq_mul]
  ring

theorem abs_centred_le (p : I) (b : Prop) : |centred (p : ℝ) b| ≤ 1 := by
  have h0 := p.2.1
  have h1 := p.2.2
  unfold centred
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- **Bounded degrees** [BKS23, `lem:balacedness-density-half` (2)]: some vertex outside `U` has
more than `degreeBound` neighbours in `U` with probability at most `δ`. Hoeffding for each
vertex, then a union bound. -/
theorem prob_not_degreeLE (p : I) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (G(V, p)).real {R | ¬ DegreeLE U (degreeBound U p δ) R} ≤ δ := by
  classical
  rcases Nat.eq_zero_or_pos Uᶜ.card with hV | hV
  · have : {R : SimpleGraph V | ¬ DegreeLE U (degreeBound U p δ) R} = ∅ := by
      ext R
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro v hv
      exact absurd hv (by rw [card_eq_zero.1 hV]; exact notMem_empty v)
    rw [this, measureReal_empty]
    exact hδ.le
  have hV' : (0 : ℝ) < Uᶜ.card := by exact_mod_cast hV
  have hL : 0 ≤ Real.log (Uᶜ.card / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ, one_mul]; exact hδ1.trans (by exact_mod_cast hV))
  set s := √(2 * U.card * Real.log (Uᶜ.card / δ))
  -- The number of neighbours, from the block of `v`.
  have hcount : ∀ (R : SimpleGraph V) (v : V) (hv : v ∉ U),
      ((U.filter (R.Adj · v)).card : ℝ) - U.card * p =
        ∑ w : {w // w ∈ U}, centred p (cut U R ⟨v, hv⟩ w) := by
    intro R v hv
    simp only [centred, cut, sum_sub_distrib, sum_const, card_univ, Fintype.card_coe,
      nsmul_eq_mul]
    congr 1
    rw [card_filter, Nat.cast_sum, ← sum_coe_sort U]
    exact sum_congr rfl fun w _ ↦ by by_cases h : R.Adj w v <;> simp [h]
  -- One vertex.
  have hvertex : ∀ v (hv : v ∉ U), (G(V, p)).real {R | degreeBound U p δ <
      ((U.filter (R.Adj · v)).card : ℝ)} ≤ δ / Uᶜ.card := by
    intro v hv
    rcases Nat.eq_zero_or_pos U.card with hU | hU
    · have : {R : SimpleGraph V | degreeBound U p δ < ((U.filter (R.Adj · v)).card : ℝ)} = ∅ := by
        ext R
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        rw [card_eq_zero.1 hU]
        simp [degreeBound]
      rw [this, measureReal_empty]
      positivity
    have hsub : {R : SimpleGraph V | degreeBound U p δ < ((U.filter (R.Adj · v)).card : ℝ)} ⊆
        cut U ⁻¹' ((fun ω ↦ ω ⟨v, hv⟩) ⁻¹'
          {x | s ≤ ∑ w : {w // w ∈ U}, centred p (x w)}) := by
      intro R hR
      simp only [Set.mem_ofPred_eq, degreeBound] at hR
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, ← hcount R v hv]
      linarith
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
    rw [measureReal_def, binomialRandom_cut_preimage U p MeasurableSet.of_discrete,
      ← Measure.map_apply (measurable_pi_apply _) MeasurableSet.of_discrete, cutLaw_eq,
      Measure.infinitePi_map_eval, ← measureReal_def]
    have hU' : (0 : ℝ) < U.card := by exact_mod_cast hU
    have h := hoeffding (μ := blockLaw V U p) (X := fun w x ↦ centred p (x w))
      (iIndepFun_infinitePi (P := fun _ ↦ Ber(True, False, p)) (X := fun _ ↦ centred p)
        fun _ ↦ Measurable.of_discrete)
      (fun w ↦ Measurable.of_discrete) zero_le_one (fun w x ↦ abs_centred_le p (x w))
      (fun w ↦ by
        rw [blockLaw, ← integral_map (measurable_pi_apply w).aemeasurable
          Measurable.of_discrete.aestronglyMeasurable, Measure.infinitePi_map_eval]
        exact integral_centred p) univ (ε := s) (Real.sqrt_nonneg _)
    refine h.trans (le_of_eq ?_)
    rw [card_univ, Fintype.card_coe, one_pow, mul_one, Real.sq_sqrt (by positivity)]
    rw [show -(2 * U.card * Real.log (Uᶜ.card / δ)) / (2 * U.card) = -Real.log (Uᶜ.card / δ) by
      field_simp]
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  -- The union bound.
  have hsub : {R : SimpleGraph V | ¬ DegreeLE U (degreeBound U p δ) R} ⊆
      ⋃ v ∈ Uᶜ, {R | degreeBound U p δ < ((U.filter (R.Adj · v)).card : ℝ)} := by
    intro R hR
    simp only [DegreeLE, Set.mem_ofPred_eq, not_forall, not_le] at hR
    obtain ⟨v, hv, hlt⟩ := hR
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨v, hv, hlt⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  calc ∑ v ∈ Uᶜ, (G(V, p)).real {R | degreeBound U p δ < ((U.filter (R.Adj · v)).card : ℝ)}
      ≤ ∑ _v ∈ Uᶜ, δ / Uᶜ.card := sum_le_sum fun v hv ↦ hvertex v (mem_compl.1 hv)
    _ = δ := by
        rw [sum_const, nsmul_eq_mul]
        field_simp

/-! ### Good cuts, and `p ≤ 1/2` -/

/-- The cut of `R` is good: balanced, with the bounds `balance`, and with degrees at most
`degreeBound`. -/
def Good (p : ℝ) (t : ℕ) (δ : ℝ) (R : SimpleGraph V) : Prop :=
  Balanced U p t (balance U p δ t) R ∧ DegreeLE U (degreeBound U p δ) R

/-- For `0 < p < 1`, the cut of `G(V, p)` is good with probability at least `1 - 2δ`. -/
theorem prob_not_good {p : I} (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (t : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : (G(V, p)).real {R | ¬ Good U p t δ R} ≤ 2 * δ := by
  have hsub : {R : SimpleGraph V | ¬ Good U p t δ R} ⊆
      {R | ¬ Balanced U p t (balance U p δ t) R} ∪ {R | ¬ DegreeLE U (degreeBound U p δ) R} := by
    intro R hR
    simp only [Good, Set.mem_ofPred_eq, not_and_or] at hR
    exact hR
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans ?_)
  linarith [prob_not_balanced U hp hp1 t hδ hδ1, prob_not_degreeLE U p hδ hδ1]

/-- `1/2` in the unit interval. -/
noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

@[simp] theorem coe_half : ((half : I) : ℝ) = 1 / 2 := rfl

/-- **The reduction of `p ≤ 1/2` to `p = 1/2`** [BKS23, `lem:result-p-small`]
(`BKS23/README.md`, item 7):
for `p ≤ 1/2`, the graph `G(V, p)` lies inside a graph whose cut is good for `p = 1/2`, with
probability at least `1 - 2δ`. The event "inside a good graph" can only be broken by adding edges,
so it is at least as likely under `G(V, p)` as under `G(V, 1/2)`
(`BKS23.Random.binomialRandom_le_of_antitone`), where the graph itself is good. -/
theorem prob_not_le_good_half {p : I} (hp : (p : ℝ) ≤ 1 / 2) (t : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    (G(V, p)).real {R | ¬ ∃ R', R ≤ R' ∧ Good U (1 / 2) t δ R'} ≤ 2 * δ := by
  set E : Set (SimpleGraph V) := {R | ∃ R', R ≤ R' ∧ Good U (1 / 2) t δ R'}
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  have hanti : ∀ R R', R ≤ R' → R' ∈ E → R ∈ E := fun R R' h ⟨R'', h', hg⟩ ↦ ⟨R'', h.trans h', hg⟩
  have hmono : (G(V, half)).real E ≤ (G(V, p)).real E := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (binomialRandom_le_of_antitone (show p ≤ half from by
        rw [← Subtype.coe_le_coe, coe_half]; exact hp) hE hanti)
  have hgood : (G(V, half)).real {R | ¬ Good U (1 / 2) t δ R} ≤ 2 * δ := by
    have := prob_not_good U (p := half) (by simp) (by norm_num) t hδ hδ1
    simpa using this
  have hsub : {R | Good U (1 / 2) t δ R} ⊆ E := fun R h ↦ ⟨R, le_rfl, h⟩
  have h1 := measureReal_mono (μ := G(V, half)) hsub (measure_ne_top _ _)
  have h2 : (G(V, half)).real {R | ¬ Good U (1 / 2) t δ R} =
      1 - (G(V, half)).real {R | Good U (1 / 2) t δ R} :=
    probReal_compl_eq_one_sub (μ := G(V, half)) (s := {R | Good U (1 / 2) t δ R})
      MeasurableSet.of_discrete
  have h3 : (G(V, p)).real {R | ¬ ∃ R', R ≤ R' ∧ Good U (1 / 2) t δ R'} = 1 - (G(V, p)).real E := by
    rw [← probReal_compl_eq_one_sub hE]
    rfl
  rw [h3]
  linarith

end BKS23.Random
