module

public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Random graphs

Probability on Mathlib's binomial random graph `G(V, p)` (`SimpleGraph.binomialRandom`), shared by
the papers (first written for [BKS23], used by [BBKS24]).

* **Coins.** `G(V, p)` is the graph of independent `p`-coins on the pairs of distinct vertices
  (`RandomGraph.binomialRandom_eq_map_graphOf`); the mass of a graph on `Fin n` is
  `p^|E| (1 - p)^(n(n-1)/2 - |E|)` (`RandomGraph.binomialRandom_real_singleton`).
* **Monotonicity in `p`.** For `p ≤ q`, an event that adding edges can only break is at least as
  likely under `G(V, p)` as under `G(V, q)` (`RandomGraph.binomialRandom_le_of_antitone`). The
  coupling: both graphs threshold the same uniform variables on the pairs.
* **The cut.** The edges between a set `U` and its complement, grouped by the outside vertex, are
  independent blocks of independent `p`-coins (`RandomGraph.map_cut_binomialRandom`,
  `RandomGraph.cutLaw_eq`).
* **Characters.** The `p`-biased character `RandomGraph.chi` of a coin, and of a set of coins in a
  block (`RandomGraph.blockChar`), with mean zero (`RandomGraph.integral_chi`,
  `RandomGraph.integral_blockChar_mul`).
* An integrand at least `b` on an event `E` has integral at least `b P(E)`
  (`RandomGraph.mul_measureReal_le_integral`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval SimpleGraph Finset

namespace RandomGraph

variable {V : Type*}

/-! ### Graphs on a finite vertex set are discrete -/

instance [Finite V] : MeasurableSingletonClass (SimpleGraph V) where
  measurableSet_singleton G := by
    have : ({G} : Set (SimpleGraph V)) = Adj ⁻¹' {G.Adj} := by
      ext H
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h ↦ h ▸ rfl, fun h ↦ SimpleGraph.ext h⟩
    rw [this]
    exact measurable_adj (measurableSet_singleton _)

/-! ### Coins on the pairs -/

/-- The possible edges: pairs of distinct vertices. -/
abbrev Pair (V : Type*) := {e : Sym2 V // ¬ e.IsDiag}

/-- The graph whose edges are the pairs `e` with `ω e`. -/
def graphOf (ω : Pair V → Prop) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ h : ¬ e.IsDiag, ω ⟨e, h⟩}

theorem graphOf_adj {ω : Pair V → Prop} {u v : V} :
    (graphOf ω).Adj u v ↔ ∃ h : u ≠ v, ω ⟨s(u, v), by simpa using h⟩ := by
  simp only [graphOf, fromEdgeSet_adj, Set.mem_ofPred_eq, Sym2.mk_isDiag_iff]
  exact ⟨fun ⟨⟨h, hω⟩, _⟩ ↦ ⟨h, hω⟩, fun ⟨h, hω⟩ ↦ ⟨⟨h, hω⟩, h⟩⟩

theorem graphOf_mono {ω ω' : Pair V → Prop} (h : ∀ e, ω e → ω' e) : graphOf ω ≤ graphOf ω' :=
  fun _ _ huv ↦ by
    obtain ⟨h₁, h₂⟩ := graphOf_adj.1 huv
    exact graphOf_adj.2 ⟨h₁, h _ h₂⟩

variable (V) in
/-- Independent `p`-coins on the pairs. -/
noncomputable def coins (p : I) : Measure (Pair V → Prop) :=
  Measure.infinitePi fun _ ↦ Ber(True, False, p)

instance (p : I) : IsProbabilityMeasure (coins V p) := by
  unfold coins
  infer_instance

/-- **`G(V, p)` is the graph of independent `p`-coins on the pairs.** -/
theorem binomialRandom_eq_map_graphOf [Countable V] (p : I) :
    G(V, p) = (coins V p).map graphOf := by
  have hrestr : Measurable fun (P : Sym2 V → Prop) (e : Pair V) ↦ P e.1 := by fun_prop
  have hgraph : Measurable (graphOf : (Pair V → Prop) → SimpleGraph V) := by
    rw [measurable_iff_adj]
    intro u v
    simp only [graphOf_adj]
    by_cases huv : u = v
    · simp [huv]
    · simp only [huv, ne_eq, not_false_eq_true, exists_true_left]
      fun_prop
  rw [binomialRandom_eq_map, setBernoulli_eq_map, Measure.map_map measurable_fromEdgeSet
    (by fun_prop)]
  have hfun : (fromEdgeSet ∘ fun P : Sym2 V → Prop ↦ {i | P i}) =
      graphOf ∘ fun (P : Sym2 V → Prop) (e : Pair V) ↦ P e.1 := by
    funext P
    ext u v
    simp only [Function.comp_apply, fromEdgeSet_adj, Set.mem_ofPred_eq, graphOf_adj]
    exact ⟨fun ⟨h, huv⟩ ↦ ⟨huv, h⟩, fun ⟨huv, h⟩ ↦ ⟨h, huv⟩⟩
  rw [hfun, ← Measure.map_map hgraph hrestr,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective, coins]
  congr 2
  funext e
  have : (e.1 ∈ Sym2.diagSetᶜ) = True := eq_true e.2
  rw [this]

theorem measurable_graphOf : Measurable (graphOf : (Pair V → Prop) → SimpleGraph V) := by
  rw [measurable_iff_adj]
  intro u v
  simp only [graphOf_adj]
  by_cases huv : u = v
  · simp [huv]
  · simp only [huv, ne_eq, not_false_eq_true, exists_true_left]
    fun_prop

/-! ### The masses of graphs -/

open Classical in
/-- The mass of a graph under `G(Fin n, p)`: `p^|E| (1 - p)^(n(n-1)/2 - |E|)`. -/
theorem binomialRandom_real_singleton {n : ℕ} (p : I) (R : SimpleGraph (Fin n)) :
    (G(Fin n, p)).real {R} =
      (p : ℝ) ^ R.edgeFinset.card * (1 - (p : ℝ)) ^ (n.choose 2 - R.edgeFinset.card) := by
  classical
  rw [measureReal_def, binomialRandom_singleton, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hcard : R.edgeSet.ncard = R.edgeFinset.card := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
  rw [hcard]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, coe_toNNReal,
    coe_symm_eq]

open Classical in
/-- Sums weighted by the masses are integrals over `G(Fin n, p)`. -/
theorem sum_mass_mul {n : ℕ} (p : I) (f : SimpleGraph (Fin n) → ℝ) :
    ∑ R, ((p : ℝ) ^ R.edgeFinset.card * (1 - (p : ℝ)) ^ (n.choose 2 - R.edgeFinset.card)) * f R =
      ∫ R, f R ∂G(Fin n, p) := by
  classical
  rw [integral_fintype Integrable.of_finite]
  exact Finset.sum_congr rfl fun R _ ↦ by rw [binomialRandom_real_singleton, smul_eq_mul]

/-! ### Monotonicity in `p` -/

variable (V) in
/-- Independent uniform variables on `[0, 1]`, one for each pair. -/
noncomputable def uniforms : Measure (Pair V → I) :=
  Measure.infinitePi fun _ ↦ volume

theorem measurable_le_const (p : I) : Measurable fun x : I ↦ x ≤ p :=
  measurable_to_prop (by
    have : (fun x : I ↦ x ≤ p) ⁻¹' {True} = Set.Iic p := by ext x; simp
    rw [this]
    exact measurableSet_Iic)

/-- A `p`-coin is a uniform variable below `p`. -/
theorem map_volume_le (p : I) : (volume : Measure I).map (· ≤ p) = Ber(True, False, p) := by
  have hm := measurable_le_const p
  have hpre : ∀ s : Set Prop, (fun x : I ↦ x ≤ p) ⁻¹' s =
      {x | (True ∈ s ∧ x ≤ p) ∨ (False ∈ s ∧ ¬ x ≤ p)} := by
    intro s
    ext x
    by_cases hx : x ≤ p
    · simp [hx]
    · have := not_le.1 hx
      simp [eq_false hx, this]
  refine eq_bernoulliMeasure (fun s hs hT hF ↦ ?_) (fun s hs hT hF ↦ ?_) (fun s hs hT hF ↦ ?_)
    (fun s hs hT hF ↦ ?_)
  · rw [Measure.map_apply hm hs, hpre]
    have : {x : I | (True ∈ s ∧ x ≤ p) ∨ (False ∈ s ∧ ¬ x ≤ p)} = Set.univ :=
      Set.eq_univ_of_forall fun x ↦ by
        simp only [hT, true_and, hF, not_le, Set.mem_ofPred_eq]
        exact le_or_gt x p
    rw [this, measure_univ]
  · rw [Measure.map_apply hm hs, hpre]
    simp only [hT, true_and, hF, false_and, or_false]
    rw [show {x : I | x ≤ p} = Set.Iic p from rfl, volume_Iic, ← ENNReal.ofReal_coe_nnreal,
      coe_toNNReal]
  · rw [Measure.map_apply hm hs, hpre]
    simp only [hT, false_and, hF, true_and, false_or, not_le]
    rw [show {x : I | p < x} = Set.Ioi p from rfl, volume_Ioi, ← ENNReal.ofReal_coe_nnreal,
      coe_toNNReal, coe_symm_eq]
  · rw [Measure.map_apply hm hs, hpre]
    simp [hT, hF]

/-- **The coupling.** `p`-coins are uniform variables below `p`. -/
theorem coins_eq_map (p : I) : coins V p = (uniforms V).map fun u e ↦ u e ≤ p := by
  rw [uniforms, Measure.infinitePi_map_pi _ (f := fun _ x ↦ x ≤ p)
    fun _ ↦ measurable_le_const p, coins]
  congr 1
  funext _
  exact (map_volume_le p).symm

theorem measurable_threshold (p : I) : Measurable fun (u : Pair V → I) (e : Pair V) ↦ u e ≤ p :=
  measurable_pi_iff.2 fun e ↦ (measurable_le_const p).comp (measurable_pi_apply e)

/-- **Monotonicity in `p`.** For `p ≤ q`, an event that adding edges can only break is at least as
likely under `G(V, p)` as under `G(V, q)`: the graphs thresholding the same uniform variables at
`p` and at `q` are nested. -/
theorem binomialRandom_le_of_antitone [Countable V] {p q : I} (hpq : p ≤ q)
    {E : Set (SimpleGraph V)} (hE : MeasurableSet E)
    (hanti : ∀ R R', R ≤ R' → R' ∈ E → R ∈ E) : G(V, q) E ≤ G(V, p) E := by
  have hmap : ∀ r : I, G(V, r) E =
      uniforms V ((fun u ↦ graphOf fun e ↦ u e ≤ r) ⁻¹' E) := by
    intro r
    rw [binomialRandom_eq_map_graphOf, coins_eq_map, Measure.map_map measurable_graphOf
      (measurable_threshold r), Measure.map_apply (measurable_graphOf.comp
        (measurable_threshold r)) hE]
    rfl
  rw [hmap, hmap]
  refine measure_mono fun u hu ↦ hanti _ _ (graphOf_mono fun e h ↦ ?_) hu
  exact le_trans h hpq

instance : IsProbabilityMeasure (uniforms V) := by
  unfold uniforms
  infer_instance

/-- **Total variation in `p`.** Events have probabilities under `G(V, p)` and `G(V, q)` within
`|pairs| |p - q|`: thresholding the same uniform variables at `p` and at `q` gives the same graph
unless some uniform variable falls between them. -/
theorem abs_binomialRandom_sub_le [Fintype V] [DecidableEq V] (p q : I) (E : Set (SimpleGraph V)) :
    |(G(V, p)).real E - (G(V, q)).real E| ≤ Fintype.card (Pair V) * |(p : ℝ) - q| := by
  wlog hqp : q ≤ p generalizing p q
  · rw [abs_sub_comm, abs_sub_comm (p : ℝ)]
    exact this q p (le_of_not_ge hqp)
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  set A : I → Set (Pair V → I) := fun r ↦ (fun u ↦ graphOf fun e ↦ u e ≤ r) ⁻¹' E with hAdef
  have hmap : ∀ r : I, (G(V, r)).real E = (uniforms V).real (A r) := by
    intro r
    rw [measureReal_def, measureReal_def, binomialRandom_eq_map_graphOf, coins_eq_map,
      Measure.map_map measurable_graphOf (measurable_threshold r), Measure.map_apply
        (measurable_graphOf.comp (measurable_threshold r)) hE]
    rfl
  set D := ⋃ e : Pair V, (fun u : Pair V → I ↦ u e) ⁻¹' Set.Ioc q p with hDdef
  have hsame : ∀ u ∉ D, (graphOf fun e ↦ u e ≤ p) = graphOf fun e ↦ u e ≤ q := by
    intro u hu
    congr 1
    funext e
    have : u e ∉ Set.Ioc q p := fun h ↦ hu (Set.mem_iUnion.2 ⟨e, h⟩)
    simp only [Set.mem_Ioc, not_and, not_le] at this
    apply propext
    constructor
    · intro h
      by_contra h'
      exact absurd (this (lt_of_not_ge h')) (not_lt.2 h)
    · intro h
      exact h.trans hqp
  have h1 : A p ⊆ A q ∪ D := by
    intro u hu
    by_cases huD : u ∈ D
    · exact Or.inr huD
    · left
      simp only [hAdef, Set.mem_preimage] at hu ⊢
      rwa [← hsame u huD]
  have h2 : A q ⊆ A p ∪ D := by
    intro u hu
    by_cases huD : u ∈ D
    · exact Or.inr huD
    · left
      simp only [hAdef, Set.mem_preimage] at hu ⊢
      rwa [hsame u huD]
  have hD : (uniforms V).real D ≤ Fintype.card (Pair V) * ((p : ℝ) - q) := by
    refine (measureReal_iUnion_fintype_le _).trans (le_of_eq ?_)
    have hone : ∀ e : Pair V, (uniforms V).real ((fun u : Pair V → I ↦ u e) ⁻¹' Set.Ioc q p) =
        (p : ℝ) - q := by
      intro e
      have hmp := measurePreserving_eval_infinitePi (fun _ : Pair V ↦ (volume : Measure I)) e
      rw [measureReal_def, uniforms, hmp.measure_preimage measurableSet_Ioc.nullMeasurableSet,
        unitInterval.volume_Ioc, ENNReal.toReal_ofReal (by simpa using hqp)]
    rw [Finset.sum_congr rfl fun e _ ↦ hone e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have u1 := (measureReal_mono (μ := uniforms V) h1 (measure_ne_top _ _)).trans
    (measureReal_union_le _ _)
  have u2 := (measureReal_mono (μ := uniforms V) h2 (measure_ne_top _ _)).trans
    (measureReal_union_le _ _)
  rw [hmap, hmap, abs_le, abs_of_nonneg (sub_nonneg.2 (show (q : ℝ) ≤ p from hqp))]
  constructor <;> linarith

/-! ### The cut -/

variable (U : Finset V)

/-- The edges between `U` and its complement, grouped by the outside vertex: `cut U R v w` says
that `w ∈ U` and `v ∉ U` are adjacent in `R`. -/
def cut (R : SimpleGraph V) (v : {v // v ∉ U}) (w : {w // w ∈ U}) : Prop :=
  R.Adj w v

theorem measurable_cut : Measurable (cut U : SimpleGraph V → _) := by
  refine measurable_pi_iff.2 fun v ↦ measurable_pi_iff.2 fun w ↦ ?_
  unfold cut
  fun_prop

variable (V) in
/-- The law of the cut: independent blocks of independent `p`-coins, one block for each vertex
outside `U`. -/
noncomputable def cutLaw (p : I) : Measure ({v // v ∉ U} → {w // w ∈ U} → Prop) :=
  Measure.infinitePi fun _ ↦ Measure.infinitePi fun _ ↦ Ber(True, False, p)

instance (p : I) : IsProbabilityMeasure (cutLaw V U p) := by
  unfold cutLaw
  infer_instance

/-- The pair of `w ∈ U` and `v ∉ U`. -/
def cutPair (x : {v // v ∉ U} × {w // w ∈ U}) : Pair V :=
  ⟨s(x.2.1, x.1.1), by
    rw [Sym2.mk_isDiag_iff]
    exact fun h ↦ x.1.2 (h ▸ x.2.2)⟩

theorem cutPair_injective : Function.Injective (cutPair U) := by
  rintro ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ ⟨⟨v', hv'⟩, ⟨w', hw'⟩⟩ h
  simp only [cutPair, Subtype.mk.injEq, Sym2.eq_iff] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd hw' hv

/-- **The law of the cut** under `G(V, p)`. -/
theorem map_cut_binomialRandom [Countable V] (p : I) : G(V, p).map (cut U) = cutLaw V U p := by
  have hfun : cut U ∘ graphOf =
      (MeasurableEquiv.curry {v // v ∉ U} {w // w ∈ U} Prop) ∘
        fun (ω : Pair V → Prop) (x : {v // v ∉ U} × {w // w ∈ U}) ↦ ω (cutPair U x) := by
    funext ω
    funext v w
    simp only [Function.comp_apply, cut, graphOf_adj, MeasurableEquiv.coe_curry,
      Function.curry_apply]
    have hne : (w : V) ≠ v := fun h ↦ v.2 (h ▸ w.2)
    simp only [hne, ne_eq, not_false_eq_true, exists_true_left]
    rfl
  rw [binomialRandom_eq_map_graphOf, Measure.map_map (measurable_cut U) measurable_graphOf, hfun,
    ← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop), coins,
    Measure.map_infinitePi_infinitePi_of_inj (cutPair_injective U)]
  exact Measure.infinitePi_map_curry (fun (_ : {v // v ∉ U}) (_ : {w // w ∈ U}) ↦
    Ber(True, False, p))

/-- Events about the cut have the same probability under `G(V, p)` and under its law. -/
theorem binomialRandom_cut_preimage [Countable V] (p : I)
    {F : Set ({v // v ∉ U} → {w // w ∈ U} → Prop)} (hF : MeasurableSet F) :
    G(V, p) (cut U ⁻¹' F) = cutLaw V U p F := by
  rw [← map_cut_binomialRandom, Measure.map_apply (measurable_cut U) hF]

/-- A nonnegative integrand that is at least `b` on an event `E` has integral at least
`b P(E)`. -/
theorem mul_measureReal_le_integral {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ) (hf0 : ∀ ω, 0 ≤ f ω) {b : ℝ}
    {E : Set Ω} (hE : MeasurableSet E) (hfE : ∀ ω ∈ E, b ≤ f ω) :
    b * μ.real E ≤ ∫ ω, f ω ∂μ := by
  have h : ∫ ω, E.indicator (fun _ ↦ b) ω ∂μ ≤ ∫ ω, f ω ∂μ := by
    refine integral_mono ((integrable_const b).indicator hE) hf fun ω ↦ ?_
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      exact hfE ω hω
    · rw [Set.indicator_of_notMem hω]
      exact hf0 ω
  rwa [integral_indicator_const _ hE, smul_eq_mul, mul_comm] at h

/-! ### Characters -/

/-- The `p`-biased character of a coin: `√((1-p)/p)` for heads, `-√(p/(1-p))` for tails. -/
noncomputable def chi (p : ℝ) (b : Prop) : ℝ := by
  classical
  exact if b then √((1 - p) / p) else -√(p / (1 - p))

/-- The characters have mean zero: `p √((1-p)/p) = (1 - p) √(p/(1-p))`. -/
theorem integral_chi {p : I} (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∫ b, chi p b ∂Ber(True, False, p) = 0 := by
  rw [integral_bernoulliMeasure]
  simp only [chi, ite_true, ite_false, smul_eq_mul]
  have h1 : 0 < 1 - (p : ℝ) := by linarith
  rw [Real.sqrt_div' _ hp.le, Real.sqrt_div' _ h1.le]
  have hsp := Real.sqrt_pos.2 hp
  have hsq := Real.sqrt_pos.2 h1
  field_simp
  rw [Real.sq_sqrt hp.le, Real.sq_sqrt h1.le]
  ring


/-! ### Characters of sets in a block -/

variable [DecidableEq V]

/-- The character `u_S(v)` of a set `S ⊆ U`, from the block `x` of coins between `v` and `U`. -/
noncomputable def blockChar (p : ℝ) (S : Finset V) (x : {w // w ∈ U} → Prop) : ℝ :=
  ∏ w ∈ S.subtype (· ∈ U), chi p (x w)

theorem card_subtype_of_subset {S : Finset V} (hS : S ⊆ U) : (S.subtype (· ∈ U)).card = S.card := by
  rw [card_subtype, filter_true_of_mem hS]

theorem blockChar_eq_prod_univ (p : ℝ) (S : Finset V) (x : {w // w ∈ U} → Prop) :
    blockChar U p S x = ∏ w : {w // w ∈ U}, if (w : V) ∈ S then chi p (x w) else 1 := by
  have h : ∀ w : {w // w ∈ U}, (if (w : V) ∈ S then chi p (x w) else 1) =
      if w ∈ S.subtype (· ∈ U) then chi p (x w) else 1 := fun w ↦ by simp only [mem_subtype]
  rw [blockChar, prod_congr rfl fun w _ ↦ h w, prod_ite_mem, univ_inter]

variable (V) in
/-- The law of a block: independent `p`-coins between one vertex and `U`. -/
noncomputable def blockLaw (p : I) : Measure ({w // w ∈ U} → Prop) :=
  Measure.infinitePi fun _ ↦ Ber(True, False, p)

instance (p : I) : IsProbabilityMeasure (blockLaw V U p) := by
  unfold blockLaw
  infer_instance

omit [DecidableEq V] in
theorem cutLaw_eq (p : I) : cutLaw V U p = Measure.infinitePi fun _ ↦ blockLaw V U p := rfl

/-- **Mean zero.** For `S ≠ T` of the same size, `u_S(v) u_T(v)` has mean zero: some `w ∈ S ∖ T`
contributes its character alone, which has mean zero. -/
theorem integral_blockChar_mul {p : I} (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {S T : Finset V}
    (hS : S ⊆ U) (hST : S ≠ T) (hcard : S.card = T.card) :
    ∫ x, blockChar U p S x * blockChar U p T x ∂blockLaw V U p = 0 := by
  have hw : ∃ w ∈ S, w ∉ T := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hST (eq_of_subset_of_card_le h hcard.ge)
  obtain ⟨w, hwS, hwT⟩ := hw
  simp_rw [blockChar_eq_prod_univ, ← prod_mul_distrib]
  rw [blockLaw, Measure.infinitePi_eq_pi, integral_fintype_prod_eq_prod
    (f := fun (w : {w // w ∈ U}) (b : Prop) ↦
      (if (w : V) ∈ S then chi p b else 1) * (if (w : V) ∈ T then chi p b else 1))]
  refine prod_eq_zero (mem_univ ⟨w, hS hwS⟩) ?_
  simp only [hwS, ite_true, hwT, ite_false, mul_one]
  exact integral_chi hp hp1

/-- The characters have second moment `1`: `p (1-p)/p + (1-p) p/(1-p) = 1`. -/
theorem integral_chi_mul_chi {p : I} (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∫ b, chi p b * chi p b ∂Ber(True, False, p) = 1 := by
  rw [integral_bernoulliMeasure]
  simp only [chi, ite_true, ite_false, smul_eq_mul]
  have h1 : 0 < 1 - (p : ℝ) := by linarith
  rw [neg_mul_neg, Real.mul_self_sqrt (div_nonneg h1.le hp.le),
    Real.mul_self_sqrt (div_nonneg hp.le h1.le)]
  field_simp
  ring

/-- **Orthogonality.** For distinct `A, B ⊆ U`, `u_A u_B` has mean zero: some `w` in exactly one
of them contributes its character alone. -/
theorem integral_blockChar_mul_of_ne {p : I} (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {A B : Finset V} (hA : A ⊆ U) (hB : B ⊆ U) (hAB : A ≠ B) :
    ∫ x, blockChar U p A x * blockChar U p B x ∂blockLaw V U p = 0 := by
  have hw : ∃ w, (w ∈ A ∧ w ∉ B) ∨ (w ∈ B ∧ w ∉ A) := by
    by_contra h
    simp only [not_exists, not_or, not_and, not_not] at h
    exact hAB (Finset.ext fun w ↦ ⟨fun hw ↦ (h w).1 hw, fun hw ↦ (h w).2 hw⟩)
  obtain ⟨w, hw⟩ := hw
  simp_rw [blockChar_eq_prod_univ, ← prod_mul_distrib]
  rw [blockLaw, Measure.infinitePi_eq_pi, integral_fintype_prod_eq_prod
    (f := fun (w : {w // w ∈ U}) (b : Prop) ↦
      (if (w : V) ∈ A then chi p b else 1) * (if (w : V) ∈ B then chi p b else 1))]
  rcases hw with ⟨hwA, hwB⟩ | ⟨hwB, hwA⟩
  · refine prod_eq_zero (mem_univ ⟨w, hA hwA⟩) ?_
    simp only [hwA, ite_true, hwB, ite_false, mul_one]
    exact integral_chi hp hp1
  · refine prod_eq_zero (mem_univ ⟨w, hB hwB⟩) ?_
    simp only [hwA, ite_false, hwB, ite_true, one_mul]
    exact integral_chi hp hp1

/-- **Normalization.** `u_A²` has mean `1`. -/
theorem integral_blockChar_mul_self {p : I} (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (A : Finset V) : ∫ x, blockChar U p A x * blockChar U p A x ∂blockLaw V U p = 1 := by
  simp_rw [blockChar_eq_prod_univ, ← prod_mul_distrib]
  rw [blockLaw, Measure.infinitePi_eq_pi, integral_fintype_prod_eq_prod
    (f := fun (w : {w // w ∈ U}) (b : Prop) ↦
      (if (w : V) ∈ A then chi p b else 1) * (if (w : V) ∈ A then chi p b else 1))]
  refine prod_eq_one fun w _ ↦ ?_
  by_cases hw : (w : V) ∈ A
  · simp only [hw, ite_true]
    exact integral_chi_mul_chi hp hp1
  · simp [hw]

/-- A bound on the characters bounds their products: `|u_A| ≤ M^|A|` for `A ⊆ U`. -/
theorem abs_blockChar_le_pow {p M : ℝ} (hM : ∀ b, |chi p b| ≤ M) {A : Finset V} (hA : A ⊆ U)
    (x : {w // w ∈ U} → Prop) : |blockChar U p A x| ≤ M ^ A.card := by
  rw [blockChar, abs_prod, ← card_subtype_of_subset U hA, ← prod_const]
  exact prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun w _ ↦ hM _

/-- The character of one coin of the block. -/
theorem blockChar_singleton (p : ℝ) {w : V} (hw : w ∈ U) (x : {w // w ∈ U} → Prop) :
    blockChar U p {w} x = chi p (x ⟨w, hw⟩) := by
  rw [blockChar_eq_prod_univ, prod_eq_single ⟨w, hw⟩]
  · simp
  · intro v _ hv
    have : (v : V) ≠ w := fun h ↦ hv (Subtype.ext h)
    simp [this]
  · simp


section Bicliques

variable [Fintype V]

/-! ### No large bicliques across the cut -/

/-- The probability that all the pairs between `A ⊆ U` and `B ⊆ Uᶜ` are edges: `p^(|A| |B|)`. -/
theorem prob_biclique (p : I) {A B : Finset V} (hA : A ⊆ U) (hB : B ⊆ Uᶜ) :
    (G(V, p)).real {R | ∀ a ∈ A, ∀ b ∈ B, R.Adj a b} = (p : ℝ) ^ (A.card * B.card) := by
  set A' : Finset {w // w ∈ U} := A.subtype (· ∈ U)
  set B' : Finset {v // v ∉ U} := B.subtype (· ∉ U)
  have hset : {R : SimpleGraph V | ∀ a ∈ A, ∀ b ∈ B, R.Adj a b} =
      cut U ⁻¹' Set.pi B' fun _ ↦ Set.pi A' fun _ ↦ {True} := by
    ext R
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, mem_coe, Set.mem_singleton_iff,
      eq_iff_iff, iff_true, cut, A', B', mem_subtype]
    constructor
    · exact fun h b hb a ha ↦ h a ha b hb
    · exact fun h a ha b hb ↦ h ⟨b, mem_compl.1 (hB hb)⟩ hb ⟨a, hA ha⟩ ha
  have hcoin : Ber(True, False, p) {True} = unitInterval.toNNReal p :=
    bernoulliMeasure_apply_of_mem_of_notMem p (MeasurableSet.of_discrete) rfl
      fun h ↦ of_eq_true (Set.mem_singleton_iff.1 h)
  have hmB : ∀ b ∈ B', MeasurableSet
      (Set.pi (A' : Set {w // w ∈ U}) fun _ ↦ ({True} : Set Prop)) :=
    fun _ _ ↦ MeasurableSet.of_discrete
  have hmA : ∀ a ∈ A', MeasurableSet ({True} : Set Prop) := fun _ _ ↦ MeasurableSet.of_discrete
  rw [hset, measureReal_def, binomialRandom_cut_preimage U p MeasurableSet.of_discrete, cutLaw,
    Measure.infinitePi_pi (fun _ ↦ Measure.infinitePi fun _ ↦ Ber(True, False, p)) hmB]
  simp_rw [Measure.infinitePi_pi (fun _ ↦ Ber(True, False, p)) hmA, hcoin, prod_const]
  rw [card_subtype_of_subset U hA]
  have hB' : B'.card = B.card := by
    rw [card_subtype, filter_true_of_mem fun b hb ↦ mem_compl.1 (hB hb)]
  rw [hB', ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.coe_toReal,
    unitInterval.coe_toNNReal, ← pow_mul]

/-- No biclique with at least `ℓ₀` vertices in `U` and at least one outside, of total size `|U|`.
A `|U|`-clique other than `U` in a graph whose cut is that of `R` meets `U` in fewer than `ℓ₀`
vertices: its part in `U` and its part outside form such a biclique. -/
def NoBiclique (ℓ₀ : ℕ) (R : SimpleGraph V) : Prop :=
  ∀ A ⊆ U, ∀ B ⊆ Uᶜ, ℓ₀ ≤ A.card → B.Nonempty → A.card + B.card = U.card →
    ∃ a ∈ A, ∃ b ∈ B, ¬ R.Adj a b

/-- **No large bicliques** [BKS23, `lem:clique-intersection`]: the first moment. A biclique with
`j ≥ 1` vertices outside `U` has `|U| - j ≥ ℓ₀` inside; there are at most `|U|^j |V|^j` of them,
each present with probability at most `p^(ℓ₀ j)`. -/
theorem prob_not_noBiclique (p : I) (ℓ₀ : ℕ) :
    (G(V, p)).real {R | ¬ NoBiclique U ℓ₀ R} ≤
      ∑ j ∈ Icc 1 U.card, ((U.card : ℝ) * Uᶜ.card * (p : ℝ) ^ ℓ₀) ^ j := by
  classical
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hsub : {R : SimpleGraph V | ¬ NoBiclique U ℓ₀ R} ⊆
      ⋃ j ∈ Icc 1 U.card, ⋃ A ∈ (U.powersetCard (U.card - j)).filter (ℓ₀ ≤ ·.card),
        ⋃ B ∈ Uᶜ.powersetCard j, {R | ∀ a ∈ A, ∀ b ∈ B, R.Adj a b} := by
    intro R hR
    simp only [NoBiclique, Set.mem_ofPred_eq, not_forall, not_exists, not_and, not_not] at hR
    obtain ⟨A, hA, B, hB, hℓ, hne, hsum, hadj⟩ := hR
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, mem_Icc, mem_filter, mem_powersetCard]
    exact ⟨B.card, ⟨hne.card_pos, by omega⟩, A, ⟨⟨hA, by omega⟩, hℓ⟩, B, ⟨hB, rfl⟩, hadj⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans (sum_le_sum fun j hj ↦ ?_))
  rw [mem_Icc] at hj
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  refine (sum_le_sum fun A hA ↦ measureReal_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ A ∈ (U.powersetCard (U.card - j)).filter (ℓ₀ ≤ ·.card),
      ∀ B ∈ Uᶜ.powersetCard j,
        (G(V, p)).real {R | ∀ a ∈ A, ∀ b ∈ B, R.Adj a b} ≤ (p : ℝ) ^ (ℓ₀ * j) := by
    intro A hA B hB
    rw [mem_filter, mem_powersetCard] at hA
    rw [mem_powersetCard] at hB
    rw [prob_biclique U p hA.1.1 hB.1, hB.2]
    exact pow_le_pow_of_le_one hp0 hp1 (Nat.mul_le_mul_right j hA.2)
  calc ∑ A ∈ (U.powersetCard (U.card - j)).filter (ℓ₀ ≤ ·.card), ∑ B ∈ Uᶜ.powersetCard j,
        (G(V, p)).real {R | ∀ a ∈ A, ∀ b ∈ B, R.Adj a b}
      ≤ ∑ _A ∈ U.powersetCard (U.card - j), ∑ _B ∈ Uᶜ.powersetCard j, (p : ℝ) ^ (ℓ₀ * j) := by
        refine (sum_le_sum fun A hA ↦ sum_le_sum fun B hB ↦ hterm A hA B hB).trans ?_
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦
          sum_nonneg fun _ _ ↦ by positivity
    _ = (U.card.choose j : ℝ) * (Uᶜ.card.choose j) * (p : ℝ) ^ (ℓ₀ * j) := by
        rw [sum_const, sum_const, card_powersetCard, card_powersetCard,
          Nat.choose_symm hj.2, nsmul_eq_mul, nsmul_eq_mul]
        ring
    _ ≤ (U.card : ℝ) ^ j * (Uᶜ.card : ℝ) ^ j * (p : ℝ) ^ (ℓ₀ * j) := by
        gcongr
        · exact_mod_cast Nat.choose_le_pow _ _
        · exact_mod_cast Nat.choose_le_pow _ _
    _ = ((U.card : ℝ) * Uᶜ.card * (p : ℝ) ^ ℓ₀) ^ j := by
        rw [mul_pow, mul_pow, ← pow_mul, mul_comm ℓ₀]


end Bicliques

end RandomGraph
