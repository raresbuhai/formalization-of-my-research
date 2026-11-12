module

public import BDT24.Alg.Defs
public import Background.GaussianCoins
public import BDT24.Alg.Coins.Count
public import BDT24.Alg.Coins.Gauss

/-!
# The coins of the algorithm

* **The fold is the rounds** (`BDT24.Alg.algB_eq_all`): with at least `rounds · lenBlk` coins,
  the algorithm says `true` exactly when every round passes on its block of `lenBlk` coins.
* **Independent rounds** (`BDT24.Alg.coinProb_algB_true`): so the probability of `true` is the
  probability that one round passes, to the power `rounds`.
* **The two tests of a round** (`BDT24.Alg.coinProb_blockTest_false_le`) and **the own sample
  from Gaussians** (`BDT24.Alg.coinProb_fwd_false`, `BDT24.Alg.coinProb_bwd_true`,
  `BDT24.Alg.coinProb_blockTest_true`): the coins of the own sample are the cells of
  independent standard Gaussians (`Gaussian.sum_cells_eq_integral`), arranged as `n` rows
  with law `N(0, I_m)` (`BDT24.Alg.gRows`; `BDT24.Alg.CN.sum_ownSample_eq_integral` in
  `BDT24/Alg/Coins/Gauss.lean`), and the coins of the two runs of the regression algorithm are
  independent of them and of each other (`BDT24/Alg/Coins/Count.lean`).
* Generalities on `coinProb` (`BDT24.Alg.coinProb_take`, `BDT24.Alg.coinProb_add_not`) and on
  the output probabilities of the PCA algorithm (`BDT24.Alg.spcaOutputProb_false_add_true`).
-/

@[expose] public section

namespace BDT24.Alg

open MeasureTheory ProbabilityTheory

/-- `n` independent rows with law `N(0, I_m)`. -/
noncomputable abbrev gRows (n m : ℕ) : Measure (Fin n → EuclideanSpace ℝ (Fin m)) :=
  Measure.pi fun _ ↦ multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)

/-- The own sample of `n` points of `m` coordinates to `q` bits read from the cells of Gaussian
rows `g`. -/
noncomputable def ownCells (n m q : ℕ) (g : Fin n → EuclideanSpace ℝ (Fin m)) : Pts :=
  List.ofFn fun i ↦ List.ofFn fun j ↦ ownVal n m q (Gaussian.cellOf (cbits n m q) (g i j))

/-! ### The fold -/

/-- A block has at least one coin. -/
theorem lenBlk_pos (e : ℕ) (x : SPCAInput) : 0 < lenBlk e x := by
  unfold lenBlk lenA
  positivity

/-- Inside a round, the coins fill the block. -/
theorem foldl_stepSt_fill (A : SLRInput × List Bool → Estimate) (e : ℕ) (x : SPCAInput)
    {j M : ℕ} (hj : j < M) (acc : Bool) (w : List Bool) :
    ∀ buf : List Bool, buf.length + w.length < lenBlk e x →
      w.foldl (stepSt A e) ⟨x, j, M, buf, acc⟩ = ⟨x, j, M, buf ++ w, acc⟩ := by
  induction w with
  | nil => intro buf _; simp
  | cons b w ih =>
    intro buf h
    simp only [List.length_cons] at h
    rw [List.foldl_cons]
    have hs : stepSt A e ⟨x, j, M, buf, acc⟩ b = ⟨x, j, M, buf ++ [b], acc⟩ := by
      simp only [stepSt]
      rw [ite_eq_left hj, ite_eq_left (by omega)]
    rw [hs, ih (buf ++ [b]) (by simp only [List.length_append, List.length_singleton]; omega)]
    simp

/-- A full block of coins runs the round, and moves to the next one or finishes. -/
theorem foldl_stepSt_block (A : SLRInput × List Bool → Estimate) (e : ℕ) (x : SPCAInput)
    {j M : ℕ} (hj : j < M) (acc : Bool) (blk : List Bool) (hblk : blk.length = lenBlk e x) :
    blk.foldl (stepSt A e) ⟨x, j, M, [], acc⟩ =
      if j + 1 < M then ⟨x, j + 1, M, [], acc && blockTest A e x blk⟩
      else doneSt (acc && blockTest A e x blk) := by
  have hL := lenBlk_pos e x
  obtain h | ⟨w, b, rfl⟩ := List.eq_nil_or_concat' blk
  · subst h
    simp only [List.length_nil] at hblk
    omega
  have hw : w.length + 1 = lenBlk e x := by simpa using hblk
  rw [List.foldl_append,
    foldl_stepSt_fill A e x hj acc w [] (by simp only [List.length_nil]; omega)]
  simp only [List.foldl_cons, List.foldl_nil, List.nil_append, stepSt]
  rw [ite_eq_left hj, ite_eq_right (by omega)]

/-- After the last round, the coins do not change the state. -/
theorem foldl_stepSt_done (A : SLRInput × List Bool → Estimate) (e : ℕ) (a : Bool)
    (w : List Bool) : w.foldl (stepSt A e) (doneSt a) = doneSt a := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [List.foldl_cons]
    have hs : stepSt A e (doneSt a) b = doneSt a := by simp [stepSt, doneSt]
    rw [hs, ih]

/-- The rounds `j, …, j + k` on consecutive blocks, when they are the last ones. -/
theorem foldl_stepSt_rounds (A : SLRInput × List Bool → Estimate) (e : ℕ) (x : SPCAInput)
    (M k : ℕ) :
    ∀ (j : ℕ) (acc : Bool) (r : List Bool), j + k + 1 = M → (k + 1) * lenBlk e x ≤ r.length →
      r.foldl (stepSt A e) ⟨x, j, M, [], acc⟩ = doneSt (acc && (List.range (k + 1)).all
        fun i ↦ blockTest A e x ((r.drop (i * lenBlk e x)).take (lenBlk e x))) := by
  induction k with
  | zero =>
    intro j acc r hj hr
    conv_lhs => rw [← List.take_append_drop (lenBlk e x) r]
    rw [List.foldl_append, foldl_stepSt_block A e x (by omega) acc _
      (by simp only [List.length_take]; omega), ite_eq_right (by omega), foldl_stepSt_done]
    simp
  | succ k ih =>
    intro j acc r hj hr
    have hL : lenBlk e x ≤ r.length := le_trans (by nlinarith) hr
    conv_lhs => rw [← List.take_append_drop (lenBlk e x) r]
    rw [List.foldl_append, foldl_stepSt_block A e x (by omega) acc _
      (by simp only [List.length_take]; omega), ite_eq_left (by omega),
      ih (j + 1) _ (r.drop (lenBlk e x)) (by omega)
        (by simp only [List.length_drop]; rw [Nat.succ_mul] at hr; omega)]
    have hf : ((fun i ↦ blockTest A e x ((r.drop (i * lenBlk e x)).take (lenBlk e x))) ∘
        Nat.succ) = fun i ↦
          blockTest A e x (((r.drop (lenBlk e x)).drop (i * lenBlk e x)).take (lenBlk e x)) := by
      funext i
      simp only [Function.comp_apply, List.drop_drop, Nat.succ_mul, Nat.add_comm (lenBlk e x)]
    rw [List.range_succ_eq_map (n := k + 1), List.all_cons, List.all_map, zero_mul,
      List.drop_zero, Bool.and_assoc, hf]

/-- **The fold is the rounds.** -/
theorem algB_eq_all (A : SLRInput × List Bool → Estimate) (e : ℕ) (x : SPCAInput)
    (r : List Bool) (h : rounds x.δ (nOf x.points) * lenBlk e x ≤ r.length) :
    algB A e (x, r) = (List.range (rounds x.δ (nOf x.points))).all fun j ↦
      blockTest A e x ((r.drop (j * lenBlk e x)).take (lenBlk e x)) := by
  unfold algB
  by_cases h0 : rounds x.δ (nOf x.points) = 0
  · have hi : initSt x = doneSt true := by simp [initSt, h0]
    rw [hi, foldl_stepSt_done, h0]
    simp [doneSt]
  · obtain ⟨k, hk⟩ : ∃ k, rounds x.δ (nOf x.points) = k + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_ne_zero h0).symm⟩
    have hi : initSt x = ⟨x, 0, rounds x.δ (nOf x.points), [], true⟩ := by
      simp [initSt, Nat.pos_of_ne_zero h0]
    rw [hi, foldl_stepSt_rounds A e x _ k 0 true r (by omega) (by rw [← hk]; exact h), hk]
    simp [doneSt]

/-- **Independent rounds.** -/
theorem coinProb_algB_true (A : SLRInput × List Bool → Estimate) (e : ℕ) (x : SPCAInput)
    (T : ℕ) (hT : rounds x.δ (nOf x.points) * lenBlk e x ≤ T) :
    coinProb T (fun c ↦ algB A e (x, c) = true) =
      coinProb (lenBlk e x) (fun b ↦ blockTest A e x b = true) ^ rounds x.δ (nOf x.points) := by
  rw [← CN.coinProb_blocks (lenBlk e x) (fun b ↦ blockTest A e x b = true) _ T hT]
  refine CN.coinProb_congr fun c ↦ ?_
  rw [algB_eq_all A e x _ (by rw [List.length_ofFn]; exact hT)]
  simp only [List.all_eq_true, List.mem_range]

/-- A round fails only if one of its tests does. -/
theorem coinProb_blockTest_false_le (A : SLRInput × List Bool → Estimate) (e : ℕ)
    (x : SPCAInput) :
    coinProb (lenBlk e x) (fun b ↦ blockTest A e x b = false) ≤
      coinProb (lenBlk e x) (fun b ↦ fwd A e x b = false) +
        coinProb (lenBlk e x) (fun b ↦ bwd A e x b = true) := by
  calc coinProb (lenBlk e x) (fun b ↦ blockTest A e x b = false)
      = coinProb (lenBlk e x) (fun b ↦ fwd A e x b = false ∨ bwd A e x b = true) :=
        CN.coinProb_congr fun c ↦ by
          unfold blockTest
          cases fwd A e x (List.ofFn c) <;> cases bwd A e x (List.ofFn c) <;> simp
    _ ≤ _ := CN.coinProb_or_le _ _ _

/-- **An event on the own sample and the later coins of a block**: the own sample is read from
Gaussian rows. -/
theorem coinProb_own (x : SPCAInput) {n m : ℕ} (hn : nOf x.points = n) (hm : mOf x.points = m)
    (a : ℕ) (H : Pts → List Bool → Prop) :
    coinProb (lenC x + a) (fun c ↦ H (ownOf x (c.take (lenC x))) (c.drop (lenC x))) =
      ∫ g, coinProb a (H (ownCells n m x.q g)) ∂(gRows n m) := by
  subst hn hm
  refine (CN.coinProb_split (lenC x) a (fun u w ↦ H (ownOf x u) w)).trans ?_
  exact CN.sum_ownSample_eq_integral _ _ _ fun u ↦ coinProb a (H u)

/-- **The first test, with the own sample from Gaussians.** -/
theorem coinProb_fwd_false (A : SLRInput × List Bool → Estimate) (e : ℕ) (x : SPCAInput)
    {n m : ℕ} (hn : nOf x.points = n) (hm : mOf x.points = m) :
    coinProb (lenBlk e x) (fun b ↦ fwd A e x b = false) =
      ∫ g, coinProb (lenA e x)
          (fun r ↦ pairTest A e x.k x.p x.q x.points (ownCells n m x.q g) r = false)
        ∂(gRows n m) := by
  have h := coinProb_own x hn hm (2 * lenA e x)
    (fun u w ↦ pairTest A e x.k x.p x.q x.points u (w.take (lenA e x)) = false)
  refine h.trans (integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_))
  exact CN.coinProb_take (lenA e x) (2 * lenA e x) (by omega)
    (fun r ↦ pairTest A e x.k x.p x.q x.points (ownCells n m x.q g) r = false)

/-- **The second test, with the own sample from Gaussians.** -/
theorem coinProb_bwd_true (A : SLRInput × List Bool → Estimate) (e : ℕ) (x : SPCAInput)
    {n m : ℕ} (hn : nOf x.points = n) (hm : mOf x.points = m) :
    coinProb (lenBlk e x) (fun b ↦ bwd A e x b = true) =
      ∫ g, coinProb (lenA e x)
          (fun r ↦ pairTest A e x.k x.p x.q (ownCells n m x.q g) x.points r = true)
        ∂(gRows n m) := by
  have h := coinProb_own x hn hm (lenA e x + lenA e x)
    (fun u w ↦ pairTest A e x.k x.p x.q u x.points ((w.drop (lenA e x)).take (lenA e x)) = true)
  have hev : (fun b ↦ bwd A e x b = true) = fun c ↦ pairTest A e x.k x.p x.q
      (ownOf x (c.take (lenC x))) x.points
      (((c.drop (lenC x)).drop (lenA e x)).take (lenA e x)) = true := by
    funext c
    rw [List.drop_drop]
    rfl
  rw [show lenBlk e x = lenC x + (lenA e x + lenA e x) by rw [lenBlk, two_mul], hev]
  refine h.trans (integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_))
  refine (CN.coinProb_drop (lenA e x) (lenA e x) (fun d ↦ pairTest A e x.k x.p x.q
    (ownCells n m x.q g) x.points (d.take (lenA e x)) = true)).trans ?_
  exact CN.coinProb_take (lenA e x) (lenA e x) le_rfl
    (fun r ↦ pairTest A e x.k x.p x.q (ownCells n m x.q g) x.points r = true)

/-- **A round passes**, with the own sample from Gaussians and independent coins for the two
tests. -/
theorem coinProb_blockTest_true (A : SLRInput × List Bool → Estimate) (e : ℕ) (x : SPCAInput)
    {n m : ℕ} (hn : nOf x.points = n) (hm : mOf x.points = m) :
    coinProb (lenBlk e x) (fun b ↦ blockTest A e x b = true) =
      ∫ g, coinProb (lenA e x)
          (fun r ↦ pairTest A e x.k x.p x.q x.points (ownCells n m x.q g) r = true) *
        coinProb (lenA e x)
          (fun r ↦ pairTest A e x.k x.p x.q (ownCells n m x.q g) x.points r = false)
        ∂(gRows n m) := by
  have h := coinProb_own x hn hm (lenA e x + lenA e x)
    (fun u w ↦ pairTest A e x.k x.p x.q x.points u (w.take (lenA e x)) = true ∧
      pairTest A e x.k x.p x.q u x.points ((w.drop (lenA e x)).take (lenA e x)) = false)
  have hev : (fun b ↦ blockTest A e x b = true) = fun c ↦
      pairTest A e x.k x.p x.q x.points (ownOf x (c.take (lenC x)))
        ((c.drop (lenC x)).take (lenA e x)) = true ∧
      pairTest A e x.k x.p x.q (ownOf x (c.take (lenC x))) x.points
        (((c.drop (lenC x)).drop (lenA e x)).take (lenA e x)) = false := by
    funext c
    rw [List.drop_drop]
    simp only [blockTest, fwd, bwd, Bool.and_eq_true, Bool.not_eq_true']
  rw [show lenBlk e x = lenC x + (lenA e x + lenA e x) by rw [lenBlk, two_mul], hev]
  refine h.trans (integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_))
  refine (CN.coinProb_and (lenA e x) (lenA e x)
    (fun r ↦ pairTest A e x.k x.p x.q x.points (ownCells n m x.q g) r = true)
    (fun d ↦ pairTest A e x.k x.p x.q (ownCells n m x.q g) x.points
      (d.take (lenA e x)) = false)).trans ?_
  rw [CN.coinProb_take (lenA e x) (lenA e x) le_rfl
    (fun r ↦ pairTest A e x.k x.p x.q (ownCells n m x.q g) x.points r = false)]

/-- An event on the first `T` of `L ≥ T` coins has its probability on `T` coins. -/
theorem coinProb_take (T L : ℕ) (hT : T ≤ L) (P : List Bool → Prop) :
    coinProb L (fun r ↦ P (r.take T)) = coinProb T P :=
  CN.coinProb_take T L hT P

/-- An event and its complement. -/
theorem coinProb_add_not (T : ℕ) (P : List Bool → Prop) :
    coinProb T P + coinProb T (fun r ↦ ¬ P r) = 1 :=
  CN.coinProb_add_not T P

/-- A function of the PCA input of a sample is measurable in the sample: the input depends on
the sample only through countably many values. -/
theorem measurable_comp_spcaInput {m : ℕ} {β : Type*} [MeasurableSpace β] (δ : ℚ) (p k q n : ℕ)
    (F : SPCAInput → β) :
    Measurable fun ω : Fin n → EuclideanSpace ℝ (Fin m) ↦ F (spcaInput δ p k q ω) := by
  have hZ : Measurable fun ω : Fin n → EuclideanSpace ℝ (Fin m) ↦
      fun j i ↦ quantize q (ω j i) := by
    refine Measurable.of_eval fun j ↦ Measurable.of_eval fun i ↦ ?_
    unfold quantize
    exact Int.measurable_floor.comp (by fun_prop)
  exact (measurable_of_countable (fun Z : Fin n → Fin m → ℤ ↦
    F ⟨δ, p, k, q, List.ofFn fun j ↦ List.ofFn fun i ↦ Z j i⟩)).comp hZ

/-- The output is `false` or `true`. -/
theorem coinProb_false_add_true (T : ℕ) (P : List Bool → Bool) :
    coinProb T (fun c ↦ P c = false) + coinProb T (fun c ↦ P c = true) = 1 := by
  rw [← CN.coinProb_add_not T (fun c ↦ P c = false)]
  congr 1
  exact CN.coinProb_congr fun c ↦ by simp

/-- The PCA algorithm says `false` or `true`. -/
theorem spcaOutputProb_false_add_true {m : ℕ} (B : SPCAInput × List Bool → Bool)
    (T : SPCAInput → ℕ) (δ : ℚ) (p k q n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) :
    spcaOutputProb B T δ p k q n S false + spcaOutputProb B T δ p k q n S true = 1 := by
  unfold spcaOutputProb
  set μ := Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 S
  set f : (Fin n → EuclideanSpace ℝ (Fin m)) → ENNReal := fun ω ↦ ENNReal.ofReal
    (coinProb (T (spcaInput δ p k q ω)) fun c ↦ B (spcaInput δ p k q ω, c) = false) with hf
  set g : (Fin n → EuclideanSpace ℝ (Fin m)) → ENNReal := fun ω ↦ ENNReal.ofReal
    (coinProb (T (spcaInput δ p k q ω)) fun c ↦ B (spcaInput δ p k q ω, c) = true) with hg
  have hfm : Measurable f := measurable_comp_spcaInput δ p k q n fun y ↦
    ENNReal.ofReal (coinProb (T y) fun c ↦ B (y, c) = false)
  have hfg : ∀ ω, f ω + g ω = 1 := fun ω ↦ by
    rw [hf, hg, ← ENNReal.ofReal_add (CN.coinProb_nonneg _ _) (CN.coinProb_nonneg _ _),
      coinProb_false_add_true, ENNReal.ofReal_one]
  have hsum : ∫⁻ ω, f ω ∂μ + ∫⁻ ω, g ω ∂μ = 1 := by
    rw [← lintegral_add_left hfm]
    simp only [hfg, lintegral_const, measure_univ, mul_one]
  have h1 : ∫⁻ ω, f ω ∂μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsum ▸ le_self_add)
  have h2 : ∫⁻ ω, g ω ∂μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hsum ▸ le_add_self)
  rw [← ENNReal.toReal_add h1 h2, hsum, ENNReal.toReal_one]

end BDT24.Alg
