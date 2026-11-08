module

public import BS23.SmallRadius.Alg
public import BS23.SmallRadius.Feasible
public import BS23.SmallRadius.RoundTable
public import Background.SumOfSquares.IdealSOS

/-!
# The facts of one round, from the solver

One round of the algorithm of [BS23, Theorem 1.3] (`BS23.SmallRadius.srRound`) runs the solver on
the program of the round and reads `Mwᵢ = Ẽ[wᵢ]` and `Mwwᵢᵢ' = Ẽ[wᵢ wᵢ']` off its output, for a
pseudo-expectation `Ẽ` with the properties of `BS23.SmallRadius.RoundPE`. This
file shows that these tables, with the true clusters `ℓ (Rem[i])` of the points
(`BS23.SmallRadius.roundData`), satisfy the hypotheses `BS23.SmallRadius.RoundData.Hyp` of the
abstract rounding lemma of [RoundTable.lean](RoundTable.lean).

**`BS23.SmallRadius.round_hyp`.** On a good frame, for remaining points `Rem` without repetitions
and a cluster `c` attaining `τ* = max_j |S_j ∩ Rem|` with `|S_c| ≤ 2 τ*`, the program of the round
with the parameters of `BS23.SmallRadius.SRFrame.Good.valid_problem` (`s`, `t`, `m = t / s`,
`K = (256 s)^t`, `Bd = 2^(4n²)`, the coefficients `b = bOf z t Lb` and a budget that cuts nothing),
the tables of every `Ẽ` with `RoundPE` satisfy `Hyp τ* γ ε err` with

* the objective slack `γ = η`, the accuracy of the solver (`BS23.SmallRadius.roundAcc`);
* the soundness error `err = 2^{-n}` (`n = Q.ne`);
* any bound `ε` on the cross mass `∑_{ℓ(Rem[i]) ≠ ℓ(Rem[i'])} Ẽ[wᵢ wᵢ']` (a hypothesis here; it
  comes from identifiability).

The fields:

* (F2) `Ẽ[wᵢ wᵢ'] ≥ -err` and `Ẽ[wᵢ] - Ẽ[wᵢ wᵢ'] = Ẽ[wᵢ (1 - wᵢ')] ≥ -err`: (B5) of
  [IdealSOS.lean](../../Background/SumOfSquares/IdealSOS.lean) (`SoS.BooleanOn.X_mul_X_nonneg`,
  `SoS.BooleanOn.X_mul_one_sub_X_nonneg`) in degree `4`, from the Boolean constraints
  (`BS23.SmallRadius.hasEq_bool`), and approximate soundness (`SoS.SosPlusIdeal.approx_ge`) at the
  accuracy `2η` of `Ẽ`. The error `2η (9 + 100 |A|) ∏ᵢ (1 + ‖fᵢ‖₂)` is at most `2^{-n}`
  (`BS23.SmallRadius.soundErr_le`): every constraint has `‖fᵢ‖₂ ≤ ‖fᵢ‖₁ ≤ 2^{|P|}` and there are
  at most `|P|` of them, so the product is at most `2^{|P| (|P| + 1)}`, while
  `η = 2^{-(n + |P| + 2)²}`.
* (F1) `∑ Ẽ[wᵢ] ≥ τ* - η`: optimality of `Ẽ` against the point evaluation
  (`SoS.Correct.ofPoint`) at the feasible point of the cluster `T = S_c ∩ Rem` (`wᵢ = 1_T(i)`),
  which satisfies the constraints exactly (`BS23.SmallRadius.SRFrame.Good.exists_feasible_point`;
  the point is the one of `BS23.SmallRadius.SRFrame.Good.valid_problem`), with objective `τ*`.
* (F3) `(∑ Ẽ[wᵢ])² ≤ ∑ᵢ ∑ᵢ' Ẽ[wᵢ wᵢ']`: `Ẽ (W - Ẽ W)² ≥ 0` for `W = ∑ wᵢ`
  (`BS23.SmallRadius.sq_sum_le_sum_sum`), exact positivity in degree `2`.
* (F5) `|S_j ∩ Rem| ≤ τ*` for every `j` (`τ*` is the maximum), `0 ≤ η ≤ τ*/2` (as `τ* ≥ 1` and
  `η ≤ 1/2`), `err ≥ 0` and `τ* ≤ |Rem|`.

`BS23.SmallRadius.RoundPE.mem_srRound_iff` restates the output of the round as the set
`roundSet` of the tables, for the pivot `BS23.SmallRadius.pivotE`, which is picked with the weights
`max (mw i) 0` of the tables (`BS23.SmallRadius.pivotE_eq_pick`).
-/

@[expose] public section

namespace BS23.SmallRadius

open MvPolynomial Finset SoS SoS.Solver Matrix
open BS23.Separating (lin lin_add isHomogeneous_lin coeffNorm1_lin_le eval_lin)

/-! ### Feasible points -/

section Point

variable {n d : ℕ} {z : Fin n → Fin d → ℚ} {b : List ℕ → ℚ} {s t m : ℕ} {K Bd : ℚ} {Lb : ℕ}

/-- **A point satisfying the equalities and the ball satisfies every constraint**: if a real point
`y` satisfies the ball, the Boolean and size equalities and the coefficient and moment equalities,
every constraint of the problem is nonnegative at `y`. -/
theorem nonneg_of_eval (y : Fin (lay n d s t Lb).N → ℝ)
    (hball : ∑ k, y k ^ 2 ≤ Bd)
    (hbool : ∀ i, y ((lay n d s t Lb).wv i) ^ 2 = y ((lay n d s t Lb).wv i))
    (hsum : y (lay n d s t Lb).sv = ∑ i, y ((lay n d s t Lb).wv i))
    (hcoef : ∀ α ∈ (lay n d s t Lb).As,
      eval y (toReal (((lay n d s t Lb).coefRaw z s Lb α).toPoly (lay n d s t Lb).N)) = 0)
    (hmom : ∀ γ ∈ gams d t Lb,
      eval y (toReal (((lay n d s t Lb).momRaw (gams d t Lb) b m K Lb γ).toPoly
        (lay n d s t Lb).N)) = 0) :
    ∀ f ∈ (problem z b s t m K Bd Lb).system, 0 ≤ eval y (toReal f) := by
  intro f hf
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hf
  change r ∈ (lay n d s t Lb).constraints z (gams d t Lb) b s m K Bd Lb at hr
  change 0 ≤ eval y (toReal (r.toPoly (lay n d s t Lb).N))
  have hneg : ∀ p : RawPoly, eval y (toReal ((RawAlg.neg p).toPoly (lay n d s t Lb).N)) =
      -eval y (toReal (p.toPoly (lay n d s t Lb).N)) := fun p => by
    rw [RawAlg.toPoly_neg, toReal_neg', eval_neg]
  rcases Lay.cases_of_mem_constraints hr with rfl | ⟨i, rfl | rfl⟩ | (rfl | rfl) |
    ⟨α, hα, rfl | rfl⟩ | ⟨γ, hγ, rfl | rfl⟩
  · rw [Lay.toPoly_ballRaw]
    simp [toReal]
    linarith
  · rw [Lay.toPoly_boolRaw]
    simp [toReal, hbool]
  · rw [hneg, Lay.toPoly_boolRaw]
    simp [toReal, hbool]
  · rw [Lay.toPoly_sumRaw]
    simp [toReal, hsum]
  · rw [hneg, Lay.toPoly_sumRaw]
    simp [toReal, hsum]
  · rw [hcoef α hα]
  · rw [hneg, hcoef α hα, neg_zero]
  · rw [hmom γ hγ]
  · rw [hneg, hmom γ hγ, neg_zero]

end Point

section Feasible

variable {n d k : ℕ} {F : SRFrame n d k} {w R Csep : ℝ} {s t : ℕ}

namespace SRFrame.Good

/-- **The feasible point of a cluster** (the point of `valid_problem`). Let the frame be good, let
the remaining points be `idx : Fin n' ↪ Fin n`, and let `c` be a cluster with `|S_c| ≤ 2 |T|`,
`T = {i : ℓ_{idx i} = c}`. Then the program of `valid_problem` has a real point at which every
constraint is nonnegative and whose weights are `wᵢ = 1_T(i)`. -/
theorem exists_feasible_point (hF : F.Good w R Csep s t) {Lb : ℕ} (hfit : Fits d s t (t / s) Lb)
    {n' : ℕ} (idx : Fin n' → Fin n) (hidx : Function.Injective idx) (c : Fin k)
    (hT : (cluster F.ℓ c).card ≤ 2 * (univ.filter fun i => F.ℓ (idx i) = c).card) :
    ∃ y : Fin (lay n' d s t Lb).N → ℝ,
      (∀ f ∈ (problem (fun i => F.z (idx i)) (bOf F.z t Lb) s t (t / s)
        (((256 * s) ^ t : ℕ) : ℚ) ((ballBd n : ℕ) : ℚ) Lb).system, 0 ≤ eval y (toReal f)) ∧
      ∀ i, y ((lay n' d s t Lb).wv i) = if F.ℓ (idx i) = c then 1 else 0 := by
  classical
  have hp := hF.params
  have hms : s * (t / s) = t := by rw [mul_comm]; exact hp.div_mul_s
  have hn'n : n' ≤ n := by simpa using Fintype.card_le_of_injective idx hidx
  have hnR := hF.n_pos_real
  set T' : Finset (Fin n') := univ.filter fun i => F.ℓ (idx i) = c with hT'
  set Tm : Finset (Fin n) := T'.map ⟨idx, hidx⟩ with hTm
  have hTmS : Tm ⊆ cluster F.ℓ c := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
    simp only [hT', Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simpa [cluster] using hi
  have hTmcard : Tm.card = T'.card := Finset.card_map _
  have hT'n : T'.card ≤ n := (Finset.card_le_univ _).trans (by simpa using hn'n)
  -- the mean
  set μv : Fin d → ℝ := F.G *ᵥ F.m c with hμv
  have hμ2 : μv ⬝ᵥ μv ≤ 20 * n := by
    have h1 := hF.G_mulVec_le (F.m c)
    have h2 := hF.radius c
    have h3 := hF.three_R_sq_le_n
    nlinarith [sq_nonneg R]
  have hμ : ∀ a, |μv a| ≤ n := fun a => by
    have h1 : μv a ^ 2 ≤ μv ⬝ᵥ μv := by
      rw [dotProduct, sq]
      exact Finset.single_le_sum (f := fun b => μv b * μv b) (fun b _ => mul_self_nonneg _)
        (Finset.mem_univ a)
    have h20 : (20 : ℝ) ≤ n := by
      have : ((2 ^ 20 : ℕ) : ℝ) ≤ n := by exact_mod_cast hp.n_ge
      push_cast at this
      linarith
    exact abs_le_of_sq_le_sq (by nlinarith) hnR.le
  -- the polynomials `H`, `B̃` and `F = K |T|^m B̃ - H^m`
  set H : MvPolynomial (Fin d) ℝ := ∑ i ∈ T', lin (F.zR (idx i) - μv) ^ (2 * s) with hH
  have hHhom : H.IsHomogeneous (2 * s) := isHomogeneous_sum_lin_pow _ _ _
  set Btil : MvPolynomial (Fin d) ℝ :=
    C (1 / ((n : ℝ) * (t : ℝ) ^ t)) * ∑ j, lin (F.zR j) ^ (2 * t) with hBtil
  have hBhom : Btil.IsHomogeneous (2 * t) := (isHomogeneous_sum_lin_pow _ _ _).C_mul _
  set Kr : ℝ := (256 * (s : ℝ)) ^ t * (T'.card : ℝ) ^ (t / s) with hKr
  set Fp : MvPolynomial (Fin d) ℝ := C Kr * Btil - H ^ (t / s) with hFp
  have hFpS : IsSumSq Fp := by
    have h := isSumSq_aeval (substT F.G) (hF.isSumSq_feas c hTmS (by rw [hTmcard]; exact hT))
    have hX : aeval (substT F.G) (∑ j ∈ Tm, lin (F.g j + F.e j) ^ (2 * s)) = H := by
      rw [map_sum, hTm, Finset.sum_map]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [hT', Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [map_pow, Function.Embedding.coeFn_mk, hF.aeval_substT_noise hi]
    rwa [map_sub, map_mul, aeval_C, MvPolynomial.algebraMap_eq, hF.aeval_substT_Bstd, map_pow,
      hX, hTmcard] at h
  have hFpdeg : Fp.totalDegree ≤ 2 * t := by
    have h1 : (H ^ (t / s)).IsHomogeneous (2 * t) := by
      have := hHhom.pow (t / s)
      rwa [mul_assoc, hms] at this
    exact ((hBhom.C_mul Kr).sub h1).totalDegree_le
  obtain ⟨Lh, hLh, hLdeg⟩ := hFpS.exists_list_of_totalDegree_le hFpdeg
  have hL := good_lay (n := n') hfit
  obtain ⟨P, hPeq, hPtr⟩ := exists_gram (d := d) hL.nodupB hL.memB Lh fun h hh =>
    Nat.le_of_mul_le_mul_left (hLdeg h hh) (by norm_num)
  have hCsum := sum_coeff_mul_powE_X (d := d) hL.nodupA hL.memA (p := H) hHhom.totalDegree_le
  have hBsum : ((gams d t Lb).map fun γ' => C ((bOf F.z t Lb γ' : ℚ) : ℝ) *
      RawAlg.powE (X : Fin d → MvPolynomial (Fin d) ℝ) γ').sum = Btil := by
    have h := sum_bOf_mul_powE_of_fits (S := MvPolynomial (Fin d) ℝ) F.z hfit X
    simp only [MvPolynomial.algebraMap_apply, eq_ratCast] at h
    rw [h, hBtil]
    push_cast
    rw [one_div]
    rfl
  set yw : Fin (lay n' d s t Lb).n → ℝ := fun i => if F.ℓ (idx i) = c then 1 else 0 with hyw
  set yμ : Fin (lay n' d s t Lb).d → ℝ := μv with hyμ
  set yC : Fin (lay n' d s t Lb).A → ℝ := fun j =>
    H.coeff (Mono.toFinsupp d ((lay n' d s t Lb).As.get j)) with hyC
  have hHw : (∑ i : Fin (lay n' d s t Lb).n, C (yw i) *
      (∑ a : Fin d, (C ((F.z (idx i) a : ℚ) : ℝ) - C (yμ a) : MvPolynomial (Fin d) ℝ) *
          X a) ^ (2 * s)) = H := by
    rw [hH, hT', Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [yw]
    split_ifs
    · rw [map_one, one_mul]
      simp only [lin, Pi.sub_apply, SRFrame.zR, map_sub, yμ]
    · rw [map_zero, zero_mul]
  have hKcast : ((((256 * s) ^ t : ℕ) : ℚ) : ℝ) * (T'.card : ℝ) ^ (t / s) = Kr := by
    rw [hKr]
    push_cast
    ring
  refine ⟨(lay n' d s t Lb).point yw yμ (T'.card : ℝ) yC P,
    nonneg_of_eval ((lay n' d s t Lb).point yw yμ (T'.card : ℝ) yC P) ?_ ?_ ?_ ?_ ?_,
    fun i => by simp only [Lay.point_wv, yw]⟩
  · rw [Lay.sum_point_sq]
    have hw : ∑ i, yw i ^ 2 ≤ n := by
      calc ∑ i, yw i ^ 2 ≤ ∑ _i : Fin (lay n' d s t Lb).n, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => by simp only [yw]; split_ifs <;> norm_num
        _ = n' := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
            rfl
        _ ≤ n := by exact_mod_cast hn'n
    have hm' : ∑ a, yμ a ^ 2 ≤ 20 * n := by
      have : ∑ a, yμ a ^ 2 = yμ ⬝ᵥ yμ := by simp [dotProduct, sq]
      rw [this]
      exact hμ2
    have hs : (T'.card : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hT'n) 2
    have hc : ∑ j, yC j ^ 2 ≤ ((n : ℝ) * (2 * (n : ℝ) ^ 3) ^ (2 * s)) ^ 2 := by
      calc ∑ j, yC j ^ 2 ≤ coeffNorm H ^ 2 :=
            sum_coeff_sq_le (d := d) hL.nodupA (fun e he => ((hL.memA e).1 he).1) H
        _ ≤ coeffNorm1 H ^ 2 :=
            pow_le_pow_left₀ (coeffNorm_nonneg _) (coeffNorm_le_coeffNorm1 H) 2
        _ ≤ _ := pow_le_pow_left₀ (coeffNorm1_nonneg _)
            (hF.coeffNorm1_sum_lin_pow_le idx T' hT'n hμ) 2
    have hKr0 : 0 ≤ Kr := by positivity
    have hKrle : Kr ≤ (256 * (s : ℝ)) ^ t * (n : ℝ) ^ (t / s) := by
      rw [hKr]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _)
        (by exact_mod_cast hT'n) _) (by positivity)
    have hg : ∑ β, ∑ c', P β c' ^ 2 ≤ (gridConst d t : ℝ) * (((t : ℝ) + 1) ^ d *
        ((256 * (s : ℝ)) ^ t * (n : ℝ) ^ (t / s) * ((d : ℝ) * n ^ 2 * t) ^ (2 * t))) := by
      have hLd : ∀ h ∈ Lh, h.totalDegree ≤ t := fun h hh =>
        Nat.le_of_mul_le_mul_left (hLdeg h hh) (by norm_num)
      refine hPtr.trans ((sum_coeffNorm_sq_le_grid Lh hLd).trans ?_)
      rw [← hLh]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      calc ∑ x : Fin d → Fin (t + 1), eval (gridPoint x) Fp
          ≤ ∑ _x : Fin d → Fin (t + 1),
              (256 * (s : ℝ)) ^ t * (n : ℝ) ^ (t / s) * ((d : ℝ) * n ^ 2 * t) ^ (2 * t) := by
            refine Finset.sum_le_sum fun x _ => ?_
            have hx : ∀ a, 0 ≤ gridPoint x a ∧ gridPoint x a ≤ t := fun a =>
              ⟨Nat.cast_nonneg _, show ((x a : ℕ) : ℝ) ≤ t by
                exact_mod_cast Nat.lt_succ_iff.1 (x a).2⟩
            have hH0 : 0 ≤ eval (gridPoint x) H := by
              rw [hH, map_sum]
              exact Finset.sum_nonneg fun i _ => by
                rw [map_pow]
                exact (even_two_mul s).pow_nonneg _
            refine (hF.eval_feas_le hx hKr0 hH0 (t / s)).trans ?_
            exact mul_le_mul_of_nonneg_right hKrle (by positivity)
        _ = ((t : ℝ) + 1) ^ d *
              ((256 * (s : ℝ)) ^ t * (n : ℝ) ^ (t / s) * ((d : ℝ) * n ^ 2 * t) ^ (2 * t)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    have hcast : ((21 * n + n ^ 2 + (n * (2 * n ^ 3) ^ (2 * s)) ^ 2 + gridConst d t *
        ((t + 1) ^ d * ((256 * s) ^ t * n ^ (t / s) * (d * n ^ 2 * t) ^ (2 * t))) : ℕ) : ℝ) ≤
        (ballBd n : ℝ) := by exact_mod_cast ball_arith hp
    push_cast at hcast
    have hBd : ((((ballBd n : ℕ) : ℚ)) : ℝ) = (ballBd n : ℝ) := Rat.cast_natCast _
    rw [hBd]
    linarith
  · intro i
    simp only [Lay.point_wv, yw]
    split_ifs <;> norm_num
  · simp only [Lay.point_sv, Lay.point_wv, yw]
    rw [Finset.sum_boole]
    rfl
  · intro α hα
    refine (Lay.eval_coefRaw hL _ _ hα).trans ?_
    simp only [Lay.point_cv, Lay.point_wv, Lay.point_mv]
    have key : (∑ j : Fin (lay n' d s t Lb).A, (C (yC j) : MvPolynomial (Fin d) ℝ) *
        RawAlg.powE (X : Fin d → MvPolynomial (Fin d) ℝ) ((lay n' d s t Lb).As.get j) -
      ∑ i : Fin (lay n' d s t Lb).n, (C (yw i) : MvPolynomial (Fin d) ℝ) *
        (∑ a : Fin d, (C ((F.z (idx i) a : ℚ) : ℝ) - C (yμ a) : MvPolynomial (Fin d) ℝ) *
          X a) ^ (2 * s)).coeff
          (Mono.toFinsupp d α) = 0 := by
      rw [hCsum, hHw, sub_self]
      rfl
    exact key
  · intro γ hγ
    refine (Lay.eval_momRaw hL _ _ _ hγ).trans ?_
    simp only [Lay.point_sv, Lay.point_cv, Lay.point_pv]
    have key : ((C ((((256 * s) ^ t : ℕ) : ℚ) * (T'.card : ℝ) ^ (t / s)) :
          MvPolynomial (Fin d) ℝ) * ((gams d t Lb).map fun γ' =>
          (C ((bOf F.z t Lb γ' : ℚ) : ℝ) : MvPolynomial (Fin d) ℝ) *
          RawAlg.powE (X : Fin d → MvPolynomial (Fin d) ℝ) γ').sum -
        (∑ j : Fin (lay n' d s t Lb).A, (C (yC j) : MvPolynomial (Fin d) ℝ) *
          RawAlg.powE (X : Fin d → MvPolynomial (Fin d) ℝ) ((lay n' d s t Lb).As.get j)) ^ (t / s) -
        ∑ c' : Fin (lay n' d s t Lb).B, (∑ β : Fin (lay n' d s t Lb).B,
          (C (P β c') : MvPolynomial (Fin d) ℝ) *
          RawAlg.powE (X : Fin d → MvPolynomial (Fin d) ℝ) ((lay n' d s t Lb).Bs.get β)) ^ 2).coeff
          (Mono.toFinsupp d γ) = 0 := by
      rw [hBsum, hCsum, hPeq, ← hLh, hFp, hKcast, sub_self]
      rfl
    exact key

/-- **The feasible point of a cluster, for the program of a round** on the points of a list `Rem`
without repetitions, with the parameters of `valid_problem`: a real point at which every
constraint is nonnegative and whose weights are `wᵢ = 1_T(i)`, `T = S_c ∩ Rem`, when
`|S_c| ≤ 2 |S_c ∩ Rem|`. -/
theorem exists_feasible_roundProb (hF : F.Good w R Csep s t) {Q : RoundPar} (hQs : Q.s = s)
    (hQt : Q.t = t) (hQm : Q.m = t / s) (hQK : Q.K = (((256 * s) ^ t : ℕ) : ℚ))
    (hQBd : Q.Bd = ((ballBd n : ℕ) : ℚ)) (hfit : Fits d s t (t / s) Q.Lb) {Rem : List (Fin n)}
    (hRem : Rem.Nodup) (c : Fin k)
    (hT : (cluster F.ℓ c).card ≤ 2 * (cluster F.ℓ c ∩ Rem.toFinset).card) :
    ∃ y : Fin (remLay Q Rem d).N → ℝ,
      (∀ f ∈ (roundProb Q F.z (bOf F.z t Q.Lb) Rem).system, 0 ≤ eval y (toReal f)) ∧
      ∀ i, y ((remLay Q Rem d).wv i) = if F.ℓ (Rem.get i) = c then 1 else 0 := by
  obtain ⟨s', t', m', K', Bd', Lb, nb, ne⟩ := Q
  dsimp only at hQs hQt hQm hQK hQBd hfit
  subst hQs hQt hQm hQK hQBd
  exact hF.exists_feasible_point hfit Rem.get (List.nodup_iff_injective_get.1 hRem) c
    (by rwa [card_filter_get_eq hRem])

end SRFrame.Good

end Feasible

/-! ### The soundness error -/

section Err

/-- The constraints of a problem, as real polynomials, have `‖f‖₂ ≤ 2^{|P|}`. -/
theorem coeffNorm_le_of_mem_map (P : Problem) {f : MvPolynomial (Fin P.numVars) ℝ}
    (hf : f ∈ P.system.map toReal) : coeffNorm f ≤ 2 ^ (encProblem P).length := by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
  have hg' : g ∈ P.2.2.1.map (RawPoly.toPoly P.numVars) := hg
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hg'
  exact (SoS.Correct.coeffNorm_le_coeffNorm1 _).trans ((SoS.Correct.coeffNorm1_toReal_le _ _).trans
    ((SoS.Correct.rawNorm1_le _).trans
      (pow_le_pow_right₀ (by norm_num) (SoS.Correct.length_encRaw_le_of_mem hr))))

/-- A problem has at most `|P|` constraints. -/
theorem length_map_system_le (P : Problem) :
    (P.system.map toReal).length ≤ (encProblem P).length := by
  rw [List.length_map]
  change (P.2.2.1.map (RawPoly.toPoly P.numVars)).length ≤ _
  rw [List.length_map]
  exact SoS.Correct.length_cons_le P

/-- **The norm product of a problem**: `∏ᵢ (1 + ‖fᵢ‖₂) ≤ 2^{(|P| + 1) |P|}`. -/
theorem prod_one_add_coeffNorm_le (P : Problem) :
    ∏ i : Fin (P.system.map toReal).length, (1 + coeffNorm ((P.system.map toReal).get i)) ≤
      2 ^ (((encProblem P).length + 1) * (encProblem P).length) := by
  set L := (encProblem P).length with hL
  calc ∏ i : Fin (P.system.map toReal).length, (1 + coeffNorm ((P.system.map toReal).get i))
      ≤ ∏ _i : Fin (P.system.map toReal).length, (2 : ℝ) ^ (L + 1) := by
        refine Finset.prod_le_prod₀ (fun i _ => add_nonneg zero_le_one (coeffNorm_nonneg _))
          (fun i _ => ?_)
        have h := coeffNorm_le_of_mem_map P (List.get_mem _ i)
        have h1 : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
        rw [pow_succ]
        linarith
    _ = (2 ^ (L + 1)) ^ (P.system.map toReal).length := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (2 ^ (L + 1)) ^ L := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (length_map_system_le P)
    _ = 2 ^ ((L + 1) * L) := by rw [← pow_mul]

theorem accOf_cast (ne : ℕ) (P : Problem) :
    (accOf ne P : ℝ) = 1 / 2 ^ accExp ne (encProblem P).length := by
  rw [accOf]
  push_cast
  rfl

/-- The accuracy `2^{-(n + |P| + 2)²}` is at most `1/2`. -/
theorem accOf_le_half (ne : ℕ) (P : Problem) : (accOf ne P : ℝ) ≤ 1 / 2 := by
  have he : 1 ≤ accExp ne (encProblem P).length := Nat.one_le_pow _ _ (by omega)
  have h2 : (2 : ℝ) ≤ 2 ^ accExp ne (encProblem P).length :=
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) he
  rw [accOf_cast]
  exact one_div_le_one_div_of_le two_pos h2

/-- **The soundness error is at most `2^{-n}`**: for the accuracy `η = 2^{-(n + |P| + 2)²}`,
`2η (9 + 100 |A|) ∏ᵢ (1 + ‖fᵢ‖₂) ≤ 2^{-n}`, where `A` is the system of `P`, as real polynomials
(the error of `SoS.SosPlusIdeal.approx_ge` with norm `M = 9` at the accuracy `2η`). -/
theorem soundErr_le (P : Problem) (ne : ℕ) :
    ((accOf ne P : ℝ) + accOf ne P) * (9 + ((P.system.map toReal).length : ℝ) * (9 + 1) ^ 2) *
      ∏ i : Fin (P.system.map toReal).length, (1 + coeffNorm ((P.system.map toReal).get i)) ≤
      1 / 2 ^ ne := by
  set L := (encProblem P).length with hL
  have hL4 : 4 ≤ L := by rw [hL, SoS.Correct.length_encProblem]; omega
  have hacc : (accOf ne P : ℝ) = 1 / 2 ^ ((ne + L + 2) ^ 2) := by
    rw [accOf_cast, accExp]
  have hLpow : 1 + (L : ℝ) * 1 ≤ (1 + 1) ^ L := one_add_mul_le_pow (by norm_num) L
  have h100 : (9 : ℝ) + ((P.system.map toReal).length : ℝ) * (9 + 1) ^ 2 ≤ 2 ^ (L + 7) := by
    have hl : (P.system.length : ℝ) ≤ L := by
      have h := length_map_system_le P
      rw [List.length_map] at h
      exact_mod_cast h
    rw [pow_add, List.length_map]
    norm_num at hLpow ⊢
    linarith
  have hprod := prod_one_add_coeffNorm_le P
  have hP0 : 0 ≤ ∏ i : Fin (P.system.map toReal).length,
      (1 + coeffNorm ((P.system.map toReal).get i)) :=
    Finset.prod_nonneg fun i _ => add_nonneg zero_le_one (coeffNorm_nonneg _)
  have hexp : 1 + (L + 7) + (L + 1) * L + ne ≤ (ne + L + 2) ^ 2 := by nlinarith
  have key : (2 : ℝ) ^ (1 + (L + 7) + (L + 1) * L) * 2 ^ ne ≤ 2 ^ ((ne + L + 2) ^ 2) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) hexp
  rw [hacc]
  have hpos : (0 : ℝ) < 1 / 2 ^ ((ne + L + 2) ^ 2) + 1 / 2 ^ ((ne + L + 2) ^ 2) := by positivity
  calc (1 / 2 ^ ((ne + L + 2) ^ 2) + 1 / 2 ^ ((ne + L + 2) ^ 2)) *
        (9 + ((P.system.map toReal).length : ℝ) * (9 + 1) ^ 2) *
        ∏ i : Fin (P.system.map toReal).length, (1 + coeffNorm ((P.system.map toReal).get i))
      ≤ (1 / 2 ^ ((ne + L + 2) ^ 2) + 1 / 2 ^ ((ne + L + 2) ^ 2)) * 2 ^ (L + 7) *
          2 ^ ((L + 1) * L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h100 hpos.le) hprod hP0 (by positivity)
    _ = 2 ^ (1 + (L + 7) + (L + 1) * L) / 2 ^ ((ne + L + 2) ^ 2) := by
        rw [pow_add, pow_add]
        ring
    _ ≤ 1 / 2 ^ ne := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith

end Err

/-! ### The facts of one round -/

section RoundFacts

variable {n d : ℕ} {Q : RoundPar} {z : Fin n → Fin d → ℚ} {b : List ℕ → ℚ} {Rem : List (Fin n)}
  {E : PseudoExpectation (Fin (remLay Q Rem d).N) (64 * Q.t)}

/-- **The weights are Boolean** in the constraints of the round, as real polynomials. -/
theorem booleanOn_roundProb :
    BooleanOn ((roundProb Q z b Rem).system.map toReal) (univ.image (remLay Q Rem d).wv) := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
  exact hasEq_bool (z := remPts z Rem) (b := b) (m := Q.m) (K := Q.K) (Bd := Q.Bd) i

theorem roundAcc_cast_nonneg : (0 : ℝ) ≤ (roundAcc Q z b Rem : ℝ) + roundAcc Q z b Rem := by
  have h : (0 : ℝ) < roundAcc Q z b Rem := by exact_mod_cast roundAcc_pos Q z b Rem
  linarith

/-- **(F2)** `Ẽ[wᵢ wᵢ'] ≥ -2^{-n}`: (B5) `wᵢ wᵢ' ≥ 0` and approximate soundness. -/
theorem RoundPE.mww_ge (hE : RoundPE Q z b Rem E) (ht : 1 ≤ Q.t) (i i' : Fin Rem.length) :
    -(1 / 2 ^ Q.ne : ℝ) ≤ E (X ((remLay Q Rem d).wv i) * X ((remLay Q Rem d).wv i')) := by
  have hB := booleanOn_roundProb (Q := Q) (z := z) (b := b) (Rem := Rem)
  have h := SosPlusIdeal.approx_ge roundAcc_cast_nonneg hE.approx.map_toReal
    (by omega : 2 * 4 ≤ 64 * Q.t)
    ((hB.X_mul_X_nonneg (mem_image_of_mem _ (mem_univ i))
      (mem_image_of_mem _ (mem_univ i'))).mono le_rfl (by norm_num : (3 : ℝ) ≤ 9))
  exact le_trans (neg_le_neg (soundErr_le (roundProb Q z b Rem) Q.ne)) h

/-- **(F2)** `Ẽ[wᵢ] - Ẽ[wᵢ wᵢ'] ≥ -2^{-n}`: (B5) `wᵢ (1 - wᵢ') ≥ 0` and approximate soundness. -/
theorem RoundPE.sub_ge (hE : RoundPE Q z b Rem E) (ht : 1 ≤ Q.t) (i i' : Fin Rem.length) :
    -(1 / 2 ^ Q.ne : ℝ) ≤
      E (X ((remLay Q Rem d).wv i)) -
        E (X ((remLay Q Rem d).wv i) * X ((remLay Q Rem d).wv i')) := by
  have hB := booleanOn_roundProb (Q := Q) (z := z) (b := b) (Rem := Rem)
  have h := SosPlusIdeal.approx_ge roundAcc_cast_nonneg hE.approx.map_toReal
    (by omega : 2 * 4 ≤ 64 * Q.t)
    (hB.X_mul_one_sub_X_nonneg (mem_image_of_mem _ (mem_univ i))
      (mem_image_of_mem _ (mem_univ i')))
  have he : E (X ((remLay Q Rem d).wv i) * (1 - X ((remLay Q Rem d).wv i'))) =
      E (X ((remLay Q Rem d).wv i)) -
        E (X ((remLay Q Rem d).wv i) * X ((remLay Q Rem d).wv i')) := by
    rw [mul_sub, mul_one, PseudoExpectation.map_sub]
  rw [← he]
  exact le_trans (neg_le_neg (soundErr_le (roundProb Q z b Rem) Q.ne)) h

/-- **(F3) Cauchy–Schwarz**, exact: `(∑ Ẽ[x_{vᵢ}])² ≤ ∑ᵢ ∑ᵢ' Ẽ[x_{vᵢ} x_{vᵢ'}]`, from
`Ẽ (W - Ẽ W)² ≥ 0` for `W = ∑ x_{vᵢ}`, in degree `2`. -/
theorem sq_sum_le_sum_sum {σ : Type*} {ℓ : ℕ} (E : PseudoExpectation σ ℓ) (hℓ : 2 ≤ ℓ)
    {ι : Type*} (S : Finset ι) (v : ι → σ) :
    (∑ i ∈ S, E (X (v i))) ^ 2 ≤ ∑ i ∈ S, ∑ i' ∈ S, E (X (v i) * X (v i')) := by
  set W : MvPolynomial σ ℝ := ∑ i ∈ S, X (v i) with hWdef
  set c := ∑ i ∈ S, E (X (v i)) with hc
  have hW : E W = c := E.map_sum _ _
  have hdeg : (W - C c).totalDegree ≤ 1 :=
    (totalDegree_sub _ _).trans (max_le (totalDegree_finsetSum_le fun i _ => (totalDegree_X _).le)
      (by rw [totalDegree_C]; omega))
  have h0 := E.map_mul_self_nonneg (f := W - C c) (by omega)
  have hexp : (W - C c) * (W - C c) = W * W - C c * W - C c * W + C c * C c := by ring
  rw [hexp, PseudoExpectation.map_add, PseudoExpectation.map_sub, PseudoExpectation.map_sub,
    PseudoExpectation.map_C_mul, PseudoExpectation.map_C_mul, PseudoExpectation.map_C, hW] at h0
  have hWW : E (W * W) = ∑ i ∈ S, ∑ i' ∈ S, E (X (v i) * X (v i')) := by
    rw [hWdef, Finset.sum_mul_sum, PseudoExpectation.map_sum]
    exact Finset.sum_congr rfl fun i _ => PseudoExpectation.map_sum _ _ _
  rw [← hWW, sq]
  linarith

/-- **(F1) Optimality** against a point: if every constraint is nonnegative at `y`, then
`∑ Ẽ[wᵢ] ≥ ∑ yᵢ - η`, since the point evaluation at `y` satisfies the constraints. -/
theorem RoundPE.obj_ge (hE : RoundPE Q z b Rem E) {y : Fin (remLay Q Rem d).N → ℝ}
    (hy : ∀ f ∈ (roundProb Q z b Rem).system, 0 ≤ eval y (toReal f)) :
    ∑ i, y ((remLay Q Rem d).wv i) - roundAcc Q z b Rem ≤ ∑ i, E (X ((remLay Q Rem d).wv i)) := by
  have hη : (0 : ℝ) ≤ roundAcc Q z b Rem := by exact_mod_cast (roundAcc_pos Q z b Rem).le
  have h := hE.opt (SoS.Correct.ofPoint (64 * Q.t) y) (SoS.Correct.ofPoint_approxSatisfies hy hη)
  simp only [SoS.Correct.ofPoint_apply, eval_X] at h
  linarith

/-- **The tables of a round**: the true cluster `lab (Rem[i])` of each remaining point,
`mw i = Ẽ[wᵢ]` and `mww i i' = Ẽ[wᵢ wᵢ']`. -/
noncomputable def roundData {k : ℕ} (lab : Fin n → Fin k) (Q : RoundPar) (Rem : List (Fin n))
    {L : ℕ} (E : PseudoExpectation (Fin (remLay Q Rem d).N) L) : RoundData Rem.length k where
  cl i := lab (Rem.get i)
  mw i := E (X ((remLay Q Rem d).wv i))
  mww i i' := E (X ((remLay Q Rem d).wv i) * X ((remLay Q Rem d).wv i'))

/-- The pivot of the round is picked with the weights `max (mw i) 0` of the tables. -/
theorem pivotE_eq_pick {k : ℕ} (lab : Fin n → Fin k) [NeZero Rem.length] {L : ℕ}
    (E : PseudoExpectation (Fin (remLay Q Rem d).N) L) (u : ℕ) :
    pivotE Q Rem E u = pick (fun i => max ((roundData lab Q Rem E).mw i) 0) Q.nb u := rfl

/-- **The output of the round is the set `roundSet` of the tables** for the pivot `pivotE`. -/
theorem RoundPE.mem_srRound_iff (hE : RoundPE Q z b Rem E) [NeZero Rem.length]
    (hnd : Rem.Nodup) {k : ℕ} (lab : Fin n → Fin k) (u : ℕ) (i : Fin Rem.length) :
    Rem.get i ∈ srRound Q z b Rem u ↔ i ∈ (roundData lab Q Rem E).roundSet (pivotE Q Rem E u) := by
  rw [hE.mem_srRound hnd u i, RoundData.mem_roundSet]
  rfl

end RoundFacts

/-! ### The hypotheses of the rounding lemma -/

section RoundHyp

variable {n d k : ℕ} {F : SRFrame n d k} {w R Csep : ℝ} {s t : ℕ}

/-- **The tables of a round satisfy the hypotheses of the rounding lemma**.

Let the frame be good, let `Rem` be the remaining points (without repetitions) and let the cluster
`c` attain `τ* = max_j |S_j ∩ Rem|`, with `|S_c| ≤ 2 τ*`. Let the parameters of the round be
those of `valid_problem` (`s`, `t`, `m = t / s`, `K = (256 s)^t`, `Bd = 2^(4n²)`,
`b = bOf z t Lb`, a budget that cuts nothing), and let `Ẽ` be a pseudo-expectation behind the round
(`RoundPE`, from `exists_roundPE`). Then for every bound `ε` on the cross mass
`∑_{ℓ(Rem[i]) ≠ ℓ(Rem[i'])} Ẽ[wᵢ wᵢ']`, the tables `roundData F.ℓ Q Rem Ẽ` satisfy
`Hyp τ* η ε 2^{-n}`, with `η` the accuracy of the solver and `n = Q.ne`. -/
theorem round_hyp (hF : F.Good w R Csep s t) {Q : RoundPar} (hQs : Q.s = s) (hQt : Q.t = t)
    (hQm : Q.m = t / s) (hQK : Q.K = (((256 * s) ^ t : ℕ) : ℚ))
    (hQBd : Q.Bd = ((ballBd n : ℕ) : ℚ)) (hfit : Fits d s t (t / s) Q.Lb) {Rem : List (Fin n)}
    (hRem : Rem.Nodup) {c : Fin k}
    (hT : (cluster F.ℓ c).card ≤ 2 * (cluster F.ℓ c ∩ Rem.toFinset).card)
    (hmax : ∀ j, (cluster F.ℓ j ∩ Rem.toFinset).card ≤ (cluster F.ℓ c ∩ Rem.toFinset).card)
    {E : PseudoExpectation (Fin (remLay Q Rem d).N) (64 * Q.t)}
    (hE : RoundPE Q F.z (bOf F.z t Q.Lb) Rem E) {ε : ℝ}
    (hcross : ∑ i, ∑ i' with F.ℓ (Rem.get i) ≠ F.ℓ (Rem.get i'),
      E (X ((remLay Q Rem d).wv i) * X ((remLay Q Rem d).wv i')) ≤ ε) :
    (roundData F.ℓ Q Rem E).Hyp ((cluster F.ℓ c ∩ Rem.toFinset).card)
      (roundAcc Q F.z (bOf F.z t Q.Lb) Rem) ε (1 / 2 ^ Q.ne) := by
  have ht : 1 ≤ Q.t := by rw [hQt]; exact hF.params.t_pos
  obtain ⟨y, hy, hyw⟩ := hF.exists_feasible_roundProb hQs hQt hQm hQK hQBd hfit hRem c hT
  have hτ : ∑ i, y ((remLay Q Rem d).wv i) = ((cluster F.ℓ c ∩ Rem.toFinset).card : ℝ) := by
    simp only [hyw]
    rw [Finset.sum_boole]
    exact_mod_cast SRFrame.Good.card_filter_get_eq hRem F.ℓ c
  have hc1 : 0 < (cluster F.ℓ c).card := by
    have h := hF.w_mul_le_card c
    have h0 : (0 : ℝ) < w * n / 2 := div_pos (mul_pos hF.w_pos hF.n_pos_real) two_pos
    exact_mod_cast h0.trans_le h
  have hτ1 : 1 ≤ (cluster F.ℓ c ∩ Rem.toFinset).card := by omega
  refine ⟨fun i i' => hE.mww_ge ht i i', fun i i' => hE.sub_ge ht i i', ?_, ?_, hcross, ?_,
    ⟨?_, ?_⟩, by positivity, ?_⟩
  · have h := hE.obj_ge hy
    rw [hτ] at h
    exact h
  · exact sq_sum_le_sum_sum E (by omega) univ _
  · intro c'
    have h1 : (roundData F.ℓ Q Rem E).csize c' = (cluster F.ℓ c' ∩ Rem.toFinset).card :=
      SRFrame.Good.card_filter_get_eq hRem F.ℓ c'
    rw [h1]
    exact_mod_cast hmax c'
  · exact_mod_cast (roundAcc_pos Q F.z (bOf F.z t Q.Lb) Rem).le
  · have h1 := accOf_le_half Q.ne (roundProb Q F.z (bOf F.z t Q.Lb) Rem)
    have h2 : (1 : ℝ) ≤ (cluster F.ℓ c ∩ Rem.toFinset).card := by exact_mod_cast hτ1
    change (accOf Q.ne (roundProb Q F.z (bOf F.z t Q.Lb) Rem) : ℝ) ≤ _
    linarith
  · exact_mod_cast (card_le_card inter_subset_right).trans (List.toFinset_card_le Rem)

end RoundHyp

end BS23.SmallRadius
