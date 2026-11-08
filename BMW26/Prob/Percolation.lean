module

public import BMW26.Prob.Coins
public import BMW26.SoS.Basic
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The percolated hypercube as coins

The model of `BMW26/Model.lean` (`BMW26.percolationProb`), on a probability space:

* `BMW26.coinMeasure d p`: independent `p`-coins indexed by `Fin d × Cube d`
  (`BMW26.isCoins_coinMeasure`); `BMW26.coinGraph ω` keeps the edge `{x, flip x i}` when the coin
  at `(i, lowPt x i)` is `true` (the coins `(i, x)` with `xᵢ = true` play no role).
* `BMW26.sum_percolationProb_eq`: the probability of a set of graphs under `Q_d(p)` is that of the
  event that `coinGraph ω` is in it.
* `BMW26.graphW_coinGraph`: the edge weights of `coinGraph ω` are the coins.
* **Half-cubes** (`BMW26.halfCoins`, `BMW26.specClose_halfW`): the half-cube `xᵢ = b` of `Q_{d+1}`
  is a copy of `Q_d` (insert `b` at position `i`), whose coins are a subfamily of the coins; the
  spectral closeness of the two halves gives that of `halfW i`.
* **Edge counts** (`BMW26.count_whp`): by Chebyshev's inequality, every direction has
  `p 2^d / 2 (1 ± 2^(-d/3))` edges with probability at least `1 - 2 d² 2^(-d/3)`.
-/

@[expose] public section

namespace BMW26

open MeasureTheory ProbabilityTheory Finset

/-- The coins of a percolated hypercube. -/
abbrev CoinSpace (d : ℕ) := Fin d × Cube d → Bool

/-- Independent `p`-coins indexed by `Fin d × Cube d`. -/
noncomputable def coinMeasure (d : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Measure (CoinSpace d) :=
  Measure.pi fun _ ↦ bernoulliMeasure true false ⟨p, hp, hp1⟩

/-- A single coin of `coinMeasure` is `true` with probability `p`. -/
theorem Perc.bernoulliMeasure_real_true {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliMeasure true false (⟨p, hp, hp1⟩ : unitInterval)).real {true} = p :=
  bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton true) rfl (by simp)

theorem isCoins_coinMeasure (d : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsCoins (coinMeasure d p hp hp1) (fun e ω ↦ ω e) p where
  isProb := by unfold coinMeasure; infer_instance
  meas e := measurable_pi_apply e
  indep := iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id
  prob_true e := by
    unfold coinMeasure
    rw [show {ω : CoinSpace d | ω e = true} = Function.eval e ⁻¹' ({true} : Set Bool) from rfl,
      (measurePreserving_eval _ e).measureReal_preimage
        (measurableSet_singleton true).nullMeasurableSet]
    exact Perc.bernoulliMeasure_real_true hp hp1

/-- The sample of `Q_d(p)` given by the coins: the edge `{x, flip x i}` is kept when the coin at
`(i, lowPt x i)` is `true`. -/
def coinGraph {d : ℕ} (ω : CoinSpace d) : SimpleGraph (Cube d) where
  Adj x y := ∃ i, y = flip x i ∧ ω (i, lowPt x i) = true
  symm := ⟨fun x y ⟨i, h, hω⟩ ↦ ⟨i, by subst h; rw [flip_flip], by subst h; rwa [lowPt_flip]⟩⟩
  loopless := ⟨fun x ⟨i, h, _⟩ ↦ flip_ne_self x i h.symm⟩

namespace Perc

/-! ### Helpers: flips, lower points, and the coin graph -/

variable {d : ℕ}

theorem flip_eq_flip_iff (x : Cube d) {i j : Fin d} : flip x i = flip x j ↔ i = j := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  by_contra hij
  have := congrFun h i
  rw [flip_apply_self, flip_apply_ne x hij] at this
  cases hx : x i <;> simp [hx] at this

theorem lowPt_apply_self (x : Cube d) (i : Fin d) : lowPt x i i = false :=
  Function.update_self ..

theorem lowPt_of_true {x : Cube d} {i : Fin d} (h : x i = true) : lowPt x i = flip x i := by
  unfold lowPt flip
  rw [h]
  rfl

/-- Adjacency along direction `i` read at the lower endpoint of the edge. -/
theorem adj_flip_iff_lowPt (G : SimpleGraph (Cube d)) (x : Cube d) (i : Fin d) :
    G.Adj x (flip x i) ↔ G.Adj (lowPt x i) (flip (lowPt x i) i) := by
  cases hx : x i
  · rw [lowPt_of_false hx]
  · rw [lowPt_of_true hx, flip_flip, G.adj_comm]

theorem coinGraph_adj_flip (ω : CoinSpace d) (x : Cube d) (i : Fin d) :
    (coinGraph ω).Adj x (flip x i) ↔ ω (i, lowPt x i) = true := by
  refine ⟨fun ⟨j, hj, hω⟩ ↦ ?_, fun h ↦ ⟨i, rfl, h⟩⟩
  obtain rfl := (flip_eq_flip_iff x).1 hj
  exact hω

end Perc

theorem coinGraph_le {d : ℕ} (ω : CoinSpace d) : coinGraph ω ≤ cube d := by
  rintro x y ⟨i, rfl, -⟩
  exact cube_adj_iff.2 ⟨i, rfl⟩

theorem graphW_coinGraph {d : ℕ} (ω : CoinSpace d) (i : Fin d) {x : Cube d} (hx : x i = false) :
    graphW (coinGraph ω) i x = coinW (fun e ω ↦ ω e) ω i x := by
  unfold graphW coinW bit
  by_cases h : ω (i, x) = true
  · rw [ite_eq_left ((Perc.coinGraph_adj_flip ω x i).2 (by rwa [lowPt_of_false hx])),
      ite_eq_left h]
  · rw [ite_eq_right (fun h' ↦ h (by rwa [Perc.coinGraph_adj_flip, lowPt_of_false hx] at h')),
      ite_eq_right h]

namespace Perc

/-! ### Helpers: the law of the coin graph -/

variable {d : ℕ}

/-- The edges of a subgraph of `Q_d`, as the lower pairs `(i, x)` (`xᵢ = false`) whose edge
`{x, flip x i}` it contains. -/
theorem card_lower_adj (H : SimpleGraph (Cube d)) [Fintype H.edgeSet] [DecidableRel H.Adj]
    (hH : H ≤ cube d) :
    (univ.filter fun e : Fin d × Cube d ↦ e.2 e.1 = false ∧ H.Adj e.2 (flip e.2 e.1)).card =
      H.edgeFinset.card := by
  refine Finset.card_bij (fun e _ ↦ s(e.2, flip e.2 e.1)) ?_ ?_ ?_
  · rintro ⟨i, x⟩ he
    simp only [mem_filter, mem_univ, true_and] at he
    simpa using he.2
  · rintro ⟨i, x⟩ he ⟨j, y⟩ he' heq
    simp only [mem_filter, mem_univ, true_and] at he he'
    dsimp only at heq
    rcases Sym2.eq_iff.1 heq with ⟨rfl, h2⟩ | ⟨h1, h2⟩
    · rw [(flip_eq_flip_iff x).1 h2]
    · exfalso
      have hxj := congrFun h1 j
      rw [flip_apply_self, he'.1] at hxj
      by_cases hij : i = j
      · subst hij
        rw [he.1] at hxj
        exact Bool.false_ne_true hxj
      · have hyj : y j = x j := by rw [← h2, flip_apply_ne x (Ne.symm hij)]
        rw [he'.1, hxj] at hyj
        exact Bool.false_ne_true hyj
  · intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      obtain ⟨i, rfl⟩ := cube_adj_iff.1 (hH he)
      refine ⟨(i, lowPt x i), ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        exact ⟨lowPt_apply_self x i, (adj_flip_iff_lowPt H x i).1 he⟩
      · cases hx : x i
        · simp only [lowPt_of_false hx]
        · simp only [lowPt_of_true hx, flip_flip, Sym2.eq_swap]

/-- The law of a `p`-coin: the event `b = true ↔ P` has probability `p` or `1 - p`. -/
theorem measureReal_iff_eq {ν : Measure Bool} [IsProbabilityMeasure ν] {p : ℝ}
    (hν : ν.real {true} = p) (P : Prop) [Decidable P] :
    ν.real {b | b = true ↔ P} = if P then p else 1 - p := by
  by_cases hP : P
  · have hs : {b : Bool | b = true ↔ P} = {true} := by
      ext b
      simp [hP]
    rw [ite_eq_left hP, hs, hν]
  · have hs : {b : Bool | b = true ↔ P} = {true}ᶜ := by
      ext b
      cases b <;> simp [hP]
    rw [ite_eq_right hP, hs, probReal_compl_eq_one_sub (measurableSet_singleton true), hν]

/-- For `H ≤ Q_d`, `coinGraph ω = H` says exactly that the coins at the lower pairs match the
edges of `H`. -/
theorem coinGraph_eq_iff {H : SimpleGraph (Cube d)} (hH : H ≤ cube d) (ω : CoinSpace d) :
    coinGraph ω = H ↔
      ∀ e : Fin d × Cube d, e.2 e.1 = false → (ω e = true ↔ H.Adj e.2 (flip e.2 e.1)) := by
  constructor
  · rintro rfl ⟨i, x⟩ hx
    rw [coinGraph_adj_flip, lowPt_of_false hx]
  · intro h
    ext x y
    constructor
    · rintro ⟨i, rfl, hω⟩
      rw [adj_flip_iff_lowPt]
      exact (h (i, lowPt x i) (lowPt_apply_self x i)).1 hω
    · intro hxy
      obtain ⟨i, rfl⟩ := cube_adj_iff.1 (hH hxy)
      rw [coinGraph_adj_flip]
      exact (h (i, lowPt x i) (lowPt_apply_self x i)).2 ((adj_flip_iff_lowPt H x i).1 hxy)

theorem measureReal_coinGraph_eq {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (H : SimpleGraph (Cube d)) :
    (coinMeasure d p hp hp1).real {ω | coinGraph ω = H} = percolationProb p H := by
  classical
  by_cases hH : H ≤ cube d
  · have hset : {ω : CoinSpace d | coinGraph ω = H} = Set.univ.pi fun e ↦
        if e.2 e.1 = false then {b | b = true ↔ H.Adj e.2 (flip e.2 e.1)} else Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, coinGraph_eq_iff hH]
      refine forall_congr' fun e ↦ ?_
      by_cases he : e.2 e.1 = false <;> simp [he]
    rw [hset, coinMeasure, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
    refine (Finset.prod_congr rfl fun e _ ↦ ?_).trans (b := ∏ e : Fin d × Cube d,
      if e.2 e.1 = false then (if H.Adj e.2 (flip e.2 e.1) then p else 1 - p) else 1) ?_
    · by_cases he : e.2 e.1 = false
      · simp only [he, ↓reduceIte]
        exact measureReal_iff_eq (bernoulliMeasure_real_true hp hp1) _
      · simp only [he, Bool.true_eq_false, ↓reduceIte, measure_univ, ENNReal.toReal_one]
    rw [← Finset.prod_filter, Finset.prod_ite, Finset.prod_const, Finset.prod_const,
      Finset.filter_filter, Finset.filter_filter, percolationProb, ite_eq_left hH]
    have hL := Finset.card_filter_add_card_filter_not
      (s := univ.filter fun e : Fin d × Cube d ↦ e.2 e.1 = false)
      (fun e ↦ H.Adj e.2 (flip e.2 e.1))
    rw [Finset.filter_filter, Finset.filter_filter] at hL
    have hH' := card_lower_adj H hH
    have hC := card_lower_adj (cube d) le_rfl
    have hC' : (univ.filter fun e : Fin d × Cube d ↦
        e.2 e.1 = false ∧ (cube d).Adj e.2 (flip e.2 e.1)) =
        univ.filter fun e : Fin d × Cube d ↦ e.2 e.1 = false :=
      Finset.filter_congr fun e _ ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, cube_adj_iff.2 ⟨e.1, rfl⟩⟩⟩
    rw [hC'] at hC
    congr 2
    omega
  · have hset : {ω : CoinSpace d | coinGraph ω = H} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro rfl
      exact hH (coinGraph_le ω)
    rw [hset, measureReal_empty, percolationProb, ite_eq_right hH]

end Perc

open Classical in
/-- **The model as coins**: the probability of a set of graphs under `Q_d(p)`. -/
theorem sum_percolationProb_eq (d : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Set (SimpleGraph (Cube d))) :
    ∑ H : SimpleGraph (Cube d), (if H ∈ S then percolationProb p H else 0) =
      (coinMeasure d p hp hp1).real {ω | coinGraph ω ∈ S} := by
  have := (isCoins_coinMeasure d hp hp1).isProb
  have hT : {ω : CoinSpace d | coinGraph ω ∈ S} =
      coinGraph ⁻¹' ↑(univ.filter fun H : SimpleGraph (Cube d) ↦ H ∈ S) := by
    ext
    simp
  rw [hT, ← sum_measureReal_preimage_singleton _ fun _ _ ↦ (Set.toFinite _).measurableSet,
    ← Finset.sum_filter]
  exact Finset.sum_congr rfl fun H _ ↦ (Perc.measureReal_coinGraph_eq hp hp1 H).symm

/-- The coins of the half-cube `xᵢ = b` of `Q_{d+1}`, as coins of `Q_d`. -/
def halfCoins {Ω : Type*} {d : ℕ} (i : Fin (d + 1)) (b : Bool)
    (a : Fin (d + 1) × Cube (d + 1) → Ω → Bool) : Fin d × Cube d → Ω → Bool :=
  fun e ω ↦ a (i.succAbove e.1, Fin.insertNth i b e.2) ω

theorem isCoins_halfCoins {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ} {p : ℝ}
    {a : Fin (d + 1) × Cube (d + 1) → Ω → Bool} (h : IsCoins μ a p) (i : Fin (d + 1)) (b : Bool) :
    IsCoins μ (halfCoins i b a) p := by
  have hf : Function.Injective fun e : Fin d × Cube d ↦
      (i.succAbove e.1, (Fin.insertNth i b e.2 : Cube (d + 1))) := by
    rintro ⟨j, y⟩ ⟨k, z⟩ hjk
    simp only [Prod.mk.injEq] at hjk ⊢
    exact ⟨Fin.succAbove_right_injective hjk.1,
      Fin.insertNth_right_injective (α := fun _ ↦ Bool) b hjk.2⟩
  exact h.precomp hf

namespace Perc

/-! ### Helpers: half-cubes -/

variable {d : ℕ}

/-- Sum over `Q_{d+1}` as a sum over the two half-cubes `xᵢ = b`. -/
theorem sum_cube_succ {M : Type*} [AddCommMonoid M] (i : Fin (d + 1)) (G : Cube (d + 1) → M) :
    ∑ x, G x = ∑ b : Bool, ∑ y : Cube d, G (Fin.insertNth i b y) := by
  rw [← (Fin.insertNthEquiv (fun _ ↦ Bool) i).sum_comp, Fintype.sum_prod_type]
  rfl

theorem flip_insertNth (i : Fin (d + 1)) (b : Bool) (y : Cube d) (k : Fin d) :
    flip (Fin.insertNth i b y : Cube (d + 1)) (i.succAbove k) = Fin.insertNth i b (flip y k) := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨l, rfl⟩
  · rw [flip_apply_ne _ (Fin.succAbove_ne j k).symm, Fin.insertNth_apply_same,
      Fin.insertNth_apply_same]
  · rw [Fin.insertNth_apply_succAbove]
    by_cases hlk : l = k
    · subst hlk
      rw [flip_apply_self, flip_apply_self, Fin.insertNth_apply_succAbove]
    · rw [flip_apply_ne _ (fun h ↦ hlk (Fin.succAbove_right_injective h)), flip_apply_ne _ hlk,
        Fin.insertNth_apply_succAbove]

/-- The energy only reads the weights at lower endpoints. -/
theorem energy_congr {w w' : Fin d → Cube d → ℝ} (h : ∀ j x, x j = false → w j x = w' j x)
    (g : Cube d → ℝ) : energy w g = energy w' g := by
  unfold energy
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun x hx ↦ ?_
  rw [h j x (Finset.mem_filter.1 hx).2]

/-- The energy without the edges of direction `i` is the sum of the energies of the two
half-cubes. -/
theorem energy_halfW (i : Fin (d + 1)) (w : Fin (d + 1) → Cube (d + 1) → ℝ)
    (g : Cube (d + 1) → ℝ) :
    energy (halfW i w) g = ∑ b : Bool, energy (fun k y ↦ w (i.succAbove k) (Fin.insertNth i b y))
      (fun y ↦ g (Fin.insertNth i b y)) := by
  unfold energy
  rw [Fin.sum_univ_succAbove _ i]
  simp only [halfW, ↓reduceIte, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_ne]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_filter, sum_cube_succ i]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  simp only [Fin.insertNth_apply_succAbove, flip_insertNth]

end Perc

/-- **Half-cubes**: spectral closeness of the two halves `xᵢ = false` and `xᵢ = true` gives that of
the graph without the edges of direction `i`, with the diagonal errors put together. -/
theorem specClose_halfW {d : ℕ} (ω : CoinSpace (d + 1)) (i : Fin (d + 1)) {p ε : ℝ}
    {D₀ D₁ : Cube d → ℝ}
    (h₀ : SpecClose (coinW (halfCoins i false fun e ω ↦ ω e) ω) 1 p ε D₀)
    (h₁ : SpecClose (coinW (halfCoins i true fun e ω ↦ ω e) ω) 1 p ε D₁) :
    SpecClose (halfW i (graphW (coinGraph ω))) (halfW i 1) p ε
      (fun x ↦ if x i then D₁ (Fin.removeNth i x) else D₀ (Fin.removeNth i x)) := by
  intro g
  set g₀ : Cube d → ℝ := fun y ↦ g (Fin.insertNth i false y)
  set g₁ : Cube d → ℝ := fun y ↦ g (Fin.insertNth i true y)
  have hE : energy (halfW i (graphW (coinGraph ω))) g =
      energy (coinW (halfCoins i false fun e ω ↦ ω e) ω) g₀ +
        energy (coinW (halfCoins i true fun e ω ↦ ω e) ω) g₁ := by
    rw [Perc.energy_halfW, Fintype.sum_bool, add_comm]
    congr 1 <;> refine Perc.energy_congr (fun k y hy ↦ ?_) _ <;>
      exact graphW_coinGraph ω _ (by rw [Fin.insertNth_apply_succAbove]; exact hy)
  have hF : energy (halfW i 1) g = energy 1 g₀ + energy 1 g₁ := by
    rw [Perc.energy_halfW, Fintype.sum_bool, add_comm]
    rfl
  have hD : ∑ x, (if x i then D₁ (Fin.removeNth i x) else D₀ (Fin.removeNth i x)) * g x ^ 2 =
      ∑ y, D₀ y * g₀ y ^ 2 + ∑ y, D₁ y * g₁ y ^ 2 := by
    rw [Perc.sum_cube_succ i, Fintype.sum_bool, add_comm]
    simp [g₀, g₁]
  have h0 := abs_le.1 (h₀ g₀)
  have h1 := abs_le.1 (h₁ g₁)
  rw [hE, hF, hD, abs_le]
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

namespace Perc

/-! ### Helpers: edge counts -/

/-- Half of the vertices have `xᵢ = false`. -/
theorem card_filter_false {d : ℕ} (i : Fin d) :
    ((univ.filter fun x : Cube d ↦ x i = false).card : ℝ) = 2 ^ d / 2 := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by have := i.pos; omega⟩
  rw [Finset.natCast_card_filter, sum_cube_succ i, Fintype.sum_bool]
  simp [Fin.insertNth_apply_same, pow_succ]

/-- The number of edges of direction `i` of the coin graph is the sum of the coins at the lower
pairs `(i, x)`. -/
theorem dirCount_coinGraph {d : ℕ} (ω : CoinSpace d) (i : Fin d) :
    (dirCount (coinGraph ω) i : ℝ) =
      ∑ x ∈ univ.filter (fun x : Cube d ↦ x i = false), bit (ω (i, x)) := by
  rw [dirCount, Finset.natCast_card_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx : x i = false
  · simp only [hx, true_and, ↓reduceIte, coinGraph_adj_flip, lowPt_of_false hx, bit]
  · simp [hx]

end Perc

/-- **Edge counts**: with probability at least `1 - 2 d² 2^(-d/3)`, every direction has
`p 2^d / 2 (1 ± 2^(-d/3))` edges. -/
theorem count_whp (d : ℕ) {p : ℝ} (hp : 1 / (d : ℝ) ≤ p) (hp1 : p ≤ 1) :
    1 - 2 * (d : ℝ) ^ 2 * (2 : ℝ) ^ (-(d : ℝ) / 3) ≤
      (coinMeasure d p ((one_div_nonneg.2 (Nat.cast_nonneg d)).trans hp) hp1).real
        {ω | ∀ i, |(dirCount (coinGraph ω) i : ℝ) - p * 2 ^ d / 2| ≤
          (2 : ℝ) ^ (-(d : ℝ) / 3) * (p * 2 ^ d / 2)} := by
  have hc := isCoins_coinMeasure d ((one_div_nonneg.2 (Nat.cast_nonneg d)).trans hp) hp1
  have := hc.isProb
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  set μ := coinMeasure d p ((one_div_nonneg.2 (Nat.cast_nonneg d)).trans hp) hp1 with hμ
  set q : ℝ := (2 : ℝ) ^ (-(d : ℝ) / 3) with hq
  have hq0 : 0 < q := by positivity
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hpd : 1 ≤ p * d := (div_le_iff₀ hdR).1 hp
  have hp0 : 0 < p := by
    by_contra h
    push Not at h
    nlinarith
  have hq3 : q ^ 3 * (2 : ℝ) ^ d = 1 := by
    rw [hq, ← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast 2 d,
      ← Real.rpow_add (by norm_num)]
    norm_num
  have hbad : ∀ i : Fin d, μ.real {ω | ¬ |(dirCount (coinGraph ω) i : ℝ) - p * 2 ^ d / 2| ≤
      q * (p * 2 ^ d / 2)} ≤ 2 * d * q := by
    intro i
    set L := univ.filter fun x : Cube d ↦ x i = false
    have hc' : IsCoins μ (fun x ω ↦ ω (i, x)) p :=
      hc.precomp (f := fun x : Cube d ↦ (i, x)) fun x y h ↦ (Prod.mk.inj h).2
    have hL : (L.card : ℝ) = 2 ^ d / 2 := Perc.card_filter_false i
    have hdev : ∀ ω : CoinSpace d, (dirCount (coinGraph ω) i : ℝ) - p * 2 ^ d / 2 =
        ∑ x ∈ L, 1 * (bit (ω (i, x)) - p) := by
      intro ω
      rw [Perc.dirCount_coinGraph, mul_div_assoc, ← hL]
      simp only [one_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    set t := (q * (p * 2 ^ d / 2)) ^ 2 with ht_def
    have ht : 0 < t := by positivity
    have hsub : {ω : CoinSpace d | ¬ |(dirCount (coinGraph ω) i : ℝ) - p * 2 ^ d / 2| ≤
        q * (p * 2 ^ d / 2)} ⊆
        {ω | t ≤ (fun v : Cube d → Bool ↦ (∑ x ∈ L, 1 * (bit (v x) - p)) ^ 2)
          (fun x ↦ ω (i, x))} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, not_le] at hω ⊢
      rw [hdev] at hω
      rw [← sq_abs]
      exact pow_le_pow_left₀ (by positivity) hω.le 2
    have hint : ∫ ω, (∑ x ∈ L, 1 * (bit (ω (i, x)) - p)) ^ 2 ∂μ =
        p * (1 - p) * ∑ x ∈ L, (1 : ℝ) ^ 2 :=
      hc'.integral_sum_sq L fun _ ↦ 1
    have hmk := hc'.measureReal_ge_le
      (F := fun v : Cube d → Bool ↦ (∑ x ∈ L, 1 * (bit (v x) - p)) ^ 2) (fun v ↦ sq_nonneg _) ht
    rw [hint] at hmk
    calc _ ≤ _ := measureReal_mono hsub
      _ ≤ _ := hmk
      _ = p * (1 - p) * (2 ^ d / 2) / t := by
        simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hL]
      _ ≤ 2 * d * q := by
        rw [div_le_iff₀ ht, ht_def]
        have e1 : 2 * d * q * (q * (p * 2 ^ d / 2)) ^ 2 =
            (p * d) * (p * 2 ^ d / 2) * (q ^ 3 * 2 ^ d) := by ring
        rw [e1, hq3, mul_one]
        have hr : (0 : ℝ) < 2 ^ d := by positivity
        have h3 : p * 2 ^ d / 2 ≤ (p * d) * (p * 2 ^ d / 2) :=
          le_mul_of_one_le_left (by positivity) hpd
        nlinarith [mul_nonneg (mul_nonneg hp0.le hp0.le) hr.le]
  have hmeas : MeasurableSet {ω : CoinSpace d | ∀ i, |(dirCount (coinGraph ω) i : ℝ) -
      p * 2 ^ d / 2| ≤ q * (p * 2 ^ d / 2)} := (Set.toFinite _).measurableSet
  have hcompl : {ω : CoinSpace d | ∀ i, |(dirCount (coinGraph ω) i : ℝ) - p * 2 ^ d / 2| ≤
      q * (p * 2 ^ d / 2)}ᶜ = ⋃ i, {ω | ¬ |(dirCount (coinGraph ω) i : ℝ) - p * 2 ^ d / 2| ≤
      q * (p * 2 ^ d / 2)} := by
    ext ω
    simp
  have h1 := probReal_compl_eq_one_sub (μ := μ) hmeas
  have h2 : μ.real {ω : CoinSpace d | ∀ i, |(dirCount (coinGraph ω) i : ℝ) - p * 2 ^ d / 2| ≤
      q * (p * 2 ^ d / 2)}ᶜ ≤ 2 * (d : ℝ) ^ 2 * q := by
    rw [hcompl]
    calc _ ≤ _ := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : Fin d, 2 * (d : ℝ) * q := Finset.sum_le_sum fun i _ ↦ hbad i
      _ = 2 * (d : ℝ) ^ 2 * q := by simp; ring
  linarith

end BMW26
