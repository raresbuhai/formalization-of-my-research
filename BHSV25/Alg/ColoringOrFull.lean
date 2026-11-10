module

public import BHSV25.Alg.ColoringFull
public import BHSV25.Alg.Coloring
public import BHSV25.Alg.IndepSetFull
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Corollary 1.4

[BHSV25, Corollary 1.4] (`BHSV25.Alg.threeColoring_independentSet_or_coloring`): there is `f`
with `f λ → 0` as `λ → 0` such that for every `λ > 0` an algorithm running in time `K · m^C`,
with `C` independent of `λ`, outputs on every regular `λ`-one-sided expander with `3` independent
sets covering all but `λ n` vertices `3` independent sets of which one has at least
`(1/2 - f λ) n` vertices or which cover all but `f λ · n` vertices.

**The algorithm** (`BHSV25.Alg.threeAlgGS`) runs the algorithm of Theorem 7.9
(`BHSV25.Alg.expAlg`), giving a partial `3`-coloring `c`, and that of Corollary 7.21
(`BHSV25.Alg.indepAlgGS`), giving an independent set `b`, and outputs `c` if `c` colors at least
`2 |b|` vertices and the coloring of `b` alone otherwise (`BHSV25.Alg.threeCombine`), as in
`BHSV25/Alg/Coloring.lean`.

**The parameters**, for `λ < 1/8` and `r = λ^{1/18}`: Theorem 7.9 with `δ = λ`, `γ = r/2` and the
upper bound `r⁹ = √λ` on the second eigenvalue, whose error is
`B (r⁹ + λ / r⁹) / (r/2)⁸ = 512 B r`; Corollary 7.21 with `c = 1` and `γ = r`, whose loss is at
most `11 r` since `√(2λ) ≤ 1/2`. The promised coloring, with its uncolored vertices in the
class `0`, is a partition proper up to `λ n` vertices (`BHSV25.Alg.exists_partition_of_coloring`).
If its classes have at most `(1/2 - r) n` vertices, the parts have at most `(1/2 - r/2) n`, and `c`
colors all but `512 B r · n`; otherwise a class is an independent set of more than `(1/2 - r) n`
vertices, and `|b| ≥ (1/2 - 11 r) n`. So `f λ = (512 B + 22) λ^{1/18}`, and `f λ = 1` for
`λ ≥ 1/8`, where only the output being a partial `3`-coloring matters.
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Filter Topology Turing.MultiTapeTM ComputableInPolyTime Finset

/-! ### The algorithm -/

/-- **The algorithm** of Corollary 1.4, for the parameters of Theorem 7.9 and of
Corollary 7.21. -/
def threeAlgGS (q : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × ℕ × ℕ × ℕ))
    (x : ℕ × List Bool) : List ℕ :=
  threeCombine (numV x) (expAlg q.1 x) (indepAlgGS q.2 x)

/-- The input of the machine: the parameters in unary, with the graph. -/
abbrev encThreeIn :
    (((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↪ List Bool :=
  encPair (encPair encExpPar Net.encGSPar) (encPair encNat encBits)

/-- The algorithm, with the colors in unary. -/
theorem threeAlgGS_unary : ComputableInPolyTime
    (fun z : (((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦
      threeAlgGS z.1 z.2) encThreeIn (encList encUnary) := by
  have hq1 : ComputableInPolyTime
      (fun z : (((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦
        z.1.1) encThreeIn encExpPar := (fst _ _).comp (fst _ _)
  have hq2 : ComputableInPolyTime
      (fun z : (((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦
        z.1.2) encThreeIn Net.encGSPar := (snd _ _).comp (fst _ _)
  have hx : ComputableInPolyTime
      (fun z : (((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦
        z.2) encThreeIn (encPair encNat encBits) := snd _ _
  have hn := numV_polytime.comp hx
  have hc0 := expAlg_unary.comp (hq1.prod hx)
  have hc : ComputableInPolyTime
      (fun z : (((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦
        expAlg z.1.1 z.2) encThreeIn (encList encUnary) := hc0
  have hb0 := indepAlgGS_polytime.comp (hq2.prod hx)
  have hb : ComputableInPolyTime
      (fun z : (((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦
        indepAlgGS z.1.2 z.2) encThreeIn encBits := hb0
  have hind : ComputableInPolyTime
      (fun z : (((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦
        threeIndepColoring (numV z.2) (indepAlgGS z.1.2 z.2)) encThreeIn (encList encUnary) := by
    unfold threeIndepColoring
    exact mapWithInput (unary_range' hn)
      (ite' (bitsGetDWithInput (hb.comp (fst _ _)) (snd _ _) false) (const 0) (const 3))
  have key := ite_decide (unary_lt' (numCol' 3 hn hc) (unary_mul' (const 2) (numTrue' hn hb)))
    hind hc
  unfold threeAlgGS threeCombine
  exact key

/-- **The algorithm runs in polynomial time**, reading its parameters in unary with the graph. -/
theorem threeAlgGS_polytime : ComputableInPolyTime
    (fun z : (((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦
      threeAlgGS z.1 z.2) encThreeIn encColoring := by
  have key := unaryList_to_binary.comp threeAlgGS_unary
  exact key

/-! ### The guarantee -/

variable (G : Graph)

/-- The output is a partial `3`-coloring whenever the coloring algorithm's is. -/
theorem isPartialColoring_threeAlgGS
    (q : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × ℕ × ℕ × ℕ))
    (hpc : G.IsPartialColoring 3 (expAlg q.1 (G.1, adjTable G))) :
    G.IsPartialColoring 3 (threeAlgGS q (G.1, adjTable G)) := by
  rw [threeAlgGS, numV_graph, threeCombine]
  split_ifs
  · exact isPartialColoring_threeIndepColoring G (isIndepSet_indepAlg _ G)
  · exact hpc

open Classical in
/-- **The promised coloring as a partition**: the uncolored vertices in the class `0`. If the
classes have at most `(1/2 - g) n` vertices and `λ ≤ g/2`, the parts have at most
`(1/2 - g/2) n`, and the uncolored vertices cover the edges inside them. -/
theorem exists_partition_of_coloring {lam g : ℝ} (hlg : lam ≤ g / 2)
    {c₀ : List ℕ} (hc₀ : G.IsColoring 3 lam c₀)
    (hsize : ∀ a < 3, (G.classSize 3 c₀ a : ℝ) ≤ (1 / 2 - g) * G.1) :
    ∃ χ : Fin G.1 → Fin 3, G.IsAlmostProper χ lam ∧
      ∀ a, ((univ.filter (χ · = a)).card : ℝ) ≤ (1 / 2 - g / 2) * G.1 := by
  set U₀ := univ.filter fun v : Fin G.1 ↦ ¬ G.color 3 c₀ v < 3 with hU₀
  have hU₀card : (U₀.card : ℝ) ≤ lam * G.1 := by
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin G.1)))
      (fun v ↦ G.color 3 c₀ v < 3)
    rw [card_univ, Fintype.card_fin] at h1
    have h2 := hc₀.2
    rw [Graph.numColored] at h2
    have h1' : ((univ.filter fun v ↦ G.color 3 c₀ v < 3).card : ℝ) + U₀.card = G.1 := by
      exact_mod_cast h1
    linarith
  set χ : Fin G.1 → Fin 3 := fun v ↦ if h : G.color 3 c₀ v < 3 then ⟨_, h⟩ else 0 with hχ
  have hχval : ∀ v, G.color 3 c₀ v < 3 → (χ v : ℕ) = G.color 3 c₀ v := by
    intro v h
    simp [hχ, h]
  refine ⟨χ, ⟨U₀, hU₀card, fun u v huv he ↦ ?_⟩, fun a ↦ ?_⟩
  · by_cases hu : G.color 3 c₀ u < 3
    · by_cases hv : G.color 3 c₀ v < 3
      · exact (hc₀.1 u v huv hu (by rw [← hχval u hu, ← hχval v hv, he])).elim
      · exact Or.inr (mem_filter.2 ⟨mem_univ _, hv⟩)
    · exact Or.inl (mem_filter.2 ⟨mem_univ _, hu⟩)
  · have hsub : univ.filter (χ · = a) ⊆ (univ.filter fun v ↦ G.color 3 c₀ v = a) ∪ U₀ := by
      intro v hv
      rw [mem_filter] at hv
      rw [mem_union]
      by_cases h : G.color 3 c₀ v < 3
      · exact Or.inl (mem_filter.2 ⟨mem_univ _, by rw [← hχval v h, hv.2]⟩)
      · exact Or.inr (mem_filter.2 ⟨mem_univ _, h⟩)
    have h1 : ((univ.filter (χ · = a)).card : ℝ) ≤
        (univ.filter fun v ↦ G.color 3 c₀ v = a).card + U₀.card := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    have h2 := hsize a a.2
    rw [Graph.classSize] at h2
    have h3 : lam * G.1 ≤ g / 2 * G.1 := mul_le_mul_of_nonneg_right hlg (Nat.cast_nonneg _)
    linarith

/-- **The guarantee of the combined algorithm**, given the guarantees of the coloring algorithm
(loss `e₁` on balanced colorings) and of the independent-set algorithm (loss `e₂` when an
independent set of `(1/2 - g) n` vertices exists), for `f ≥ e₁` and `f ≥ 2 e₂`. -/
theorem threeAlgGS_spec {lam g e₁ e₂ f : ℝ} (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (hf1 : e₁ ≤ f)
    (hf2 : 2 * e₂ ≤ f) (q : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × ℕ × ℕ × ℕ))
    (hpc₁ : G.IsPartialColoring 3 (expAlg q.1 (G.1, adjTable G)))
    (hcorr₁ : ∀ c₀ : List ℕ, G.IsColoring 3 lam c₀ →
      (∀ a < 3, (G.classSize 3 c₀ a : ℝ) ≤ (1 / 2 - g) * G.1) →
      (1 - e₁) * G.1 ≤ G.numColored 3 (expAlg q.1 (G.1, adjTable G)))
    (hcorr₂ : G.HasIndepSet ((1 / 2 - g) * G.1) →
      (1 / 2 - e₂) * G.1 ≤ (G.vertexSet (indepAlgGS q.2 (G.1, adjTable G))).card)
    (hcol : G.HasColoring 3 lam) :
    G.IsPartialColoring 3 (threeAlgGS q (G.1, adjTable G)) ∧
      ((∃ a < 3, (1 / 2 - f) * G.1 ≤ G.classSize 3 (threeAlgGS q (G.1, adjTable G)) a) ∨
        (1 - f) * G.1 ≤ G.numColored 3 (threeAlgGS q (G.1, adjTable G))) := by
  obtain ⟨c₀, hc₀⟩ := hcol
  have hnR : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
  refine ⟨isPartialColoring_threeAlgGS G q hpc₁, ?_⟩
  set c := expAlg q.1 (G.1, adjTable G) with hc
  set b := indepAlgGS q.2 (G.1, adjTable G) with hb
  have hrun : threeAlgGS q (G.1, adjTable G) = threeCombine G.1 c b := by
    rw [threeAlgGS, numV_graph]
  have hpc₂ := isPartialColoring_threeIndepColoring G (isIndepSet_indepAlg (indepNet q.2) G)
  have hsize₂ : (G.classSize 3 (threeIndepColoring G.1 b) 0 : ℝ) = numTrue G.1 b := by
    rw [classSize_threeIndepColoring]
  have hnum₁ : (G.numColored 3 c : ℝ) = numCol G.1 3 c := by rw [numColored_eq_numCol]
  have hcardb : ((G.vertexSet b).card : ℝ) = numTrue G.1 b := by rw [card_vertexSet]
  have hlarge : (¬ ∀ a < 3, (G.classSize 3 c₀ a : ℝ) ≤ (1 / 2 - g) * G.1) →
      (1 / 2 - e₂) * G.1 ≤ numTrue G.1 b := by
    intro hbal
    push Not at hbal
    obtain ⟨a, ha, hbig⟩ := hbal
    have hI : G.HasIndepSet ((1 / 2 - g) * G.1) := by
      refine ⟨threeClass G c₀ a, isIndepSet_threeClass G hc₀.1 a, ?_⟩
      rw [card_threeClass G c₀ ha]
      exact hbig.le
    have := hcorr₂ hI
    rw [hcardb] at this
    exact this
  have hfe1 := mul_le_mul_of_nonneg_right hf1 hnR
  have hfe2 := mul_le_mul_of_nonneg_right hf2 hnR
  have he1n := mul_nonneg he₁ hnR
  have he2n := mul_nonneg he₂ hnR
  rw [hrun, threeCombine]
  by_cases hcmp : numCol G.1 3 c < 2 * numTrue G.1 b
  · rw [ite_eq_left hcmp]
    refine Or.inl ⟨0, by norm_num, ?_⟩
    rw [hsize₂]
    have hcmp' : (numCol G.1 3 c : ℝ) < 2 * (numTrue G.1 b : ℝ) := by exact_mod_cast hcmp
    by_cases hbal : ∀ a < 3, (G.classSize 3 c₀ a : ℝ) ≤ (1 / 2 - g) * G.1
    · have h1 := hcorr₁ c₀ hc₀ hbal
      nlinarith
    · have h3 := hlarge hbal
      nlinarith
  · rw [ite_eq_right hcmp]
    refine Or.inr ?_
    have hcmp' : 2 * (numTrue G.1 b : ℝ) ≤ (numCol G.1 3 c : ℝ) := by
      exact_mod_cast not_lt.1 hcmp
    by_cases hbal : ∀ a < 3, (G.classSize 3 c₀ a : ℝ) ≤ (1 / 2 - g) * G.1
    · have h1 := hcorr₁ c₀ hc₀ hbal
      nlinarith
    · have h3 := hlarge hbal
      nlinarith

/-! ### The loss -/

/-- `λ^{1/18}`. -/
noncomputable def root18 (lam : ℝ) : ℝ := lam ^ ((18 : ℕ) : ℝ)⁻¹

theorem root18_pow {lam : ℝ} (h : 0 ≤ lam) : root18 lam ^ 18 = lam :=
  Real.rpow_inv_natCast_pow h (by norm_num)

theorem tendsto_root18 : Tendsto root18 (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto root18 (𝓝 0) (𝓝 0) := by
    have := Real.continuousAt_rpow_const 0 ((18 : ℕ) : ℝ)⁻¹ (Or.inr (by positivity))
    rw [ContinuousAt, Real.zero_rpow (by positivity)] at this
    exact this
  exact h.mono_left nhdsWithin_le_nhds

/-- **The loss of Corollary 1.4**: `(512 B + 22) λ^{1/18}` for `λ < 1/8`, `1` otherwise. -/
noncomputable def orLoss (lam : ℝ) : ℝ :=
  if lam < 1 / 8 then (512 * 42467332 + 22) * root18 lam else 1

theorem tendsto_orLoss : Tendsto orLoss (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_root18.const_mul (512 * 42467332 + 22 : ℝ)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by norm_num)] with lam hlam
  rw [orLoss, ite_eq_left hlam.2]

/-- The error of Theorem 7.9 for `δ = r¹⁸`, `γ = r/2` and the bound `r⁹`: `512 B r`. -/
theorem or_error_eq {r : ℝ} (hr : 0 < r) :
    42467332 * (r ^ 9 + r ^ 18 / r ^ 9) / (r / 2) ^ 8 = 512 * 42467332 * r := by
  field_simp
  ring

/-! ### Corollary 1.4 -/

open Classical in
/-- **Corollary 1.4** of [BHSV25]: for every `λ > 0`, an algorithm running in time `K · m^C`, with
`C` independent of `λ`, that, on regular `λ`-one-sided expanders with `3` independent sets
covering all but `λ n` vertices, outputs `3` independent sets of which one has at least
`(1/2 - f λ) n` vertices or which cover all but `f λ · n` vertices, where `f λ → 0` as
`λ → 0`. -/
theorem threeColoring_independentSet_or_coloring :
    ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧ ∃ C : ℕ,
      ∀ lam : ℝ, 0 < lam → ∃ K : ℝ,
        ∃ A : Graph → List ℕ, RunsInTime A encGraph encColoring K C ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.HasColoring 3 lam →
            G.IsPartialColoring 3 (A G) ∧
            ((∃ a < 3, (1 / 2 - f lam) * G.1 ≤ G.classSize 3 (A G) a) ∨
              (1 - f lam) * G.1 ≤ G.numColored 3 (A G)) := by
  obtain ⟨C, hrun⟩ := exists_runsInTime_graph_fix
    (V := fun z : (((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × ℕ × ℕ × ℕ)) ×
      (ℕ × List Bool) ↦ threeAlgGS z.1 z.2) threeAlgGS_polytime
  refine ⟨orLoss, tendsto_orLoss, C, fun lam hl0 ↦ ?_⟩
  by_cases hl : lam < 1 / 8
  · -- the parameters for `r = λ^{1/18}`
    obtain ⟨r, hr⟩ : ∃ x : ℝ, x = root18 lam := ⟨_, rfl⟩
    have hr18 : r ^ 18 = lam := hr ▸ root18_pow hl0.le
    have hr0 : 0 < r := hr ▸ Real.rpow_pos_of_pos hl0 _
    have hr9 : r ^ 9 < 1 / 2 := by
      have h1 : (r ^ 9) ^ 2 < (1 / 2) ^ 2 := by
        rw [← pow_mul, hr18]
        linarith
      exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) h1
    have hr1 : r < 1 := by
      by_contra h
      have : (1 : ℝ) ≤ r ^ 9 := one_le_pow₀ (not_lt.1 h)
      linarith
    have hr9l : lam ≤ r ^ 9 := by
      rw [← hr18, show r ^ 18 = r ^ 9 * r ^ 9 by ring]
      have : 0 < r ^ 9 := by positivity
      nlinarith
    have hlr : lam ≤ r / 2 := by
      have h17 : r ^ 17 ≤ r ^ 9 := pow_le_pow_of_le_one hr0.le hr1.le (by norm_num)
      rw [← hr18, show r ^ 18 = r * r ^ 17 by ring]
      nlinarith
    have hsq : Real.sqrt (2 * lam) ≤ 1 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      linarith
    obtain ⟨p₁, hpc₁, hp₁⟩ := exists_three_params (δ := lam) (γ := r / 2) (lam := r ^ 9)
      hl0.le (by positivity) (by linarith) (by positivity) hr9
    obtain ⟨p₂, hp₂⟩ := exists_indep_params_top (c := 1) one_pos hl0 (by linarith) 1 hr0
    obtain ⟨K, hK⟩ := hrun (p₁, p₂)
    refine ⟨K, _, hK, fun G hreg hexp hcol ↦ ?_⟩
    rw [orLoss, ite_eq_left hl]
    refine threeAlgGS_spec G (e₁ := 512 * 42467332 * r) (e₂ := 11 * r) (g := r) (by positivity)
      (by positivity) (by nlinarith) (by nlinarith) (p₁, p₂) (hpc₁ G) (fun c₀ hc₀ hbal ↦ ?_)
      (fun hInd ↦ ?_) hcol
    · -- the coloring algorithm
      obtain ⟨χ, hχ, hsize⟩ := exists_partition_of_coloring G hlr hc₀ hbal
      have hexp' : G.IsOneSidedExpander (r ^ 9) :=
        (Finset.card_le_card fun i hi ↦ by
          rw [Finset.mem_filter] at hi ⊢
          exact ⟨hi.1, lt_of_le_of_lt hr9l hi.2⟩).trans hexp
      have h := (hp₁ G hreg hexp' ⟨χ, hχ, by simpa [div_div] using hsize⟩).2
      rw [← hr18, or_error_eq hr0] at h
      exact h
    · -- the independent-set algorithm
      have h := hp₂ G hreg hexp hInd
      have h1 : (4 + 1) * r / (1 - Real.sqrt (2 * lam)) ≤ 10 * r := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      have h2 : (1 / 2 - 11 * r) * G.1 ≤ (1 / 2 - r - (4 + 1) * r / (1 - Real.sqrt (2 * lam))) *
          G.1 := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      exact h2.trans h
  · -- `λ ≥ 1/8`: only the output being a partial coloring matters
    obtain ⟨K, hK⟩ := hrun (((3, 3, 0, 0, 0), (0, 0, 0, 0)), (0, 0, 0, 0))
    refine ⟨K, _, hK, fun G _ _ _ ↦ ⟨isPartialColoring_threeAlgGS G _
      (isPartialColoring_gridAlg G (by norm_num) le_rfl _ _ _ _), Or.inr ?_⟩⟩
    rw [orLoss, ite_eq_right hl, sub_self, zero_mul]
    exact Nat.cast_nonneg _

end Alg

end BHSV25
