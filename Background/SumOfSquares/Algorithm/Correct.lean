module

public import Background.SumOfSquares.Algorithm.PolyTime
public import Background.SumOfSquares.Algorithm.Padding
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# The algorithm is correct

`SoS.Correct.core_correct`: on a valid problem and accuracies `η, γ > 0`, the algorithm with the
budget `SoS.Solver.budget` outputs a correct answer (`SoS.Solver.Correct`).

* **The budget suffices** for valid problems: the number of variables and the degree are not
  capped, and the budgeted lists of `Background/SumOfSquares/Algorithm/Core.lean` are the exact ones
  (`SoS.Correct.ctx_eq`).
* **Sizes.** Every quantity of the argument (moment bounds, coefficient norms, the accuracies) is
  between `2^-Z` and `2^(Z²)`, for the size `Z` of the input and the budget.
* **The ellipsoid method** (`Ellipsoid.exists_feasible_le`) runs on the coordinates, with the
  oracle of `Background/SumOfSquares/Algorithm/Oracle.lean` and the step of
  `Background/SumOfSquares/Algorithm/Loop.lean`; every competitor gives a ball of good points
  (`SoS.Lifted.exists_lift`, `SoS.Lifted.mem_of_near`). So the best center is in the relaxed set,
  with almost the smallest objective.
* **The output** (`SoS.Lifted.output`, `SoS.Lifted.abs_obj_mix_sub_le`) mixes it with the grid
  moments.
-/

@[expose] public section

namespace SoS.Correct

open MvPolynomial SoS.Solver SoS.Poly SoS.Coords SoS.Oracle SoS.Loop SoS.Core SoS.Lifted
open Encoding (encRat)

/-! ### Point evaluations -/

section Point

variable {σ : Type*} {ℓ : ℕ}

/-- The evaluation at a point, a pseudo-expectation of every degree. -/
noncomputable def ofPoint (ℓ : ℕ) (y : σ → ℝ) : PseudoExpectation σ ℓ where
  toLinearMap := (aeval y).toLinearMap
  map_one' := by simp
  map_mul_self_nonneg' f _ := by simp [mul_self_nonneg]

theorem ofPoint_apply (y : σ → ℝ) (f : MvPolynomial σ ℝ) : ofPoint ℓ y f = eval y f := by
  simp [ofPoint]

theorem eval_nonneg_of_isSumSq {h : MvPolynomial σ ℝ} (hh : IsSumSq h) (y : σ → ℝ) :
    0 ≤ eval y h := by
  induction hh with
  | zero => simp
  | sq_add a _ ih =>
    rw [eval_add, eval_mul]
    nlinarith [mul_self_nonneg (eval y a)]

/-- **A point where the constraints hold satisfies them**, approximately for every `η ≥ 0`. -/
theorem ofPoint_approxSatisfies {K : Type*} [Field K] [Algebra K ℝ] {A : System σ K}
    {y : σ → ℝ} (hy : ∀ f ∈ A, 0 ≤ eval y (toReal f)) {η : ℝ} (hη : 0 ≤ η) :
    (ofPoint ℓ y).ApproxSatisfies A η 0 := by
  intro S h hh _
  rw [ofPoint_apply, eval_mul, System.prod, toReal_prod, map_prod]
  have h1 : 0 ≤ eval y h := eval_nonneg_of_isSumSq hh y
  have h2 : 0 ≤ ∏ i ∈ S, eval y (toReal (A.get i)) :=
    Finset.prod_nonneg fun i _ => hy _ (List.get_mem A i)
  have h3 : 0 ≤ η * coeffNorm h * ∏ i ∈ S, coeffNorm (toReal (A.get i)) :=
    mul_nonneg (mul_nonneg hη (coeffNorm_nonneg _)) (Finset.prod_nonneg fun _ _ =>
      coeffNorm_nonneg _)
  linarith [mul_nonneg h1 h2]

end Point

/-! ### Sizes of the encodings -/

theorem encProblem_apply (P : Problem) : encProblem P = SoS.PolyTime.encProblemM P := rfl

theorem length_encProblem (P : Problem) : (encProblem P).length =
    2 * (Turing.MultiTapeTM.encNat P.1).length + 1 +
      (2 * (Turing.MultiTapeTM.encNat P.2.1).length + 1 +
        (2 * (Turing.MultiTapeTM.encList encRaw P.2.2.1).length + 1 +
          (2 * (encRaw P.2.2.2.1).length + 1 +
            (Turing.MultiTapeTM.encList encRaw P.2.2.2.2).length))) := by
  rw [encProblem_apply]
  simp only [SoS.PolyTime.encProblemM, Turing.MultiTapeTM.length_encPair]

theorem length_encList_le_of_mem {α : Type} (e : α ↪ List Bool) {l : List α} {a : α}
    (ha : a ∈ l) : (e a).length ≤ (Turing.MultiTapeTM.encList e l).length :=
  Turing.MultiTapeTM.SizedListEncoding.length_elem_le l a ha

theorem length_le_encList {α : Type} (e : α ↪ List Bool) (l : List α) :
    l.length ≤ (Turing.MultiTapeTM.encList e l).length :=
  Turing.MultiTapeTM.SizedListEncoding.length_le (encA := e)
    (encL := Turing.MultiTapeTM.encList e) l

/-- The constraints are no longer than the problem. -/
theorem length_encList_cons_le (P : Problem) :
    (Turing.MultiTapeTM.encList encRaw P.2.2.1).length ≤ (encProblem P).length := by
  rw [length_encProblem]; omega

theorem length_encRaw_le_of_mem {P : Problem} {f : RawPoly} (hf : f ∈ P.2.2.1) :
    (encRaw f).length ≤ (encProblem P).length :=
  (length_encList_le_of_mem encRaw hf).trans (length_encList_cons_le P)

theorem length_le_encRaw (f : RawPoly) : f.length ≤ (encRaw f).length :=
  length_le_encList _ f

theorem length_cons_le (P : Problem) : P.2.2.1.length ≤ (encProblem P).length :=
  (length_le_encList encRaw _).trans (length_encList_cons_le P)

/-- The objective polynomials are no longer than the problem. -/
theorem length_encRaw_obj_le {P : Problem} {q : RawPoly} (hq : q ∈ P.2.2.2.1 :: P.2.2.2.2) :
    (encRaw q).length ≤ (encProblem P).length := by
  rw [length_encProblem]
  rcases List.mem_cons.1 hq with rfl | hq
  · omega
  · have := length_encList_le_of_mem encRaw hq
    omega

/-! ### The number of variables -/

theorem card_support_toPoly_le (n : ℕ) (p : RawPoly) : (p.toPoly n).support.card ≤ p.length := by
  classical
  have hsub : (p.toPoly n).support ⊆ p.toFinset.image fun t => Mono.toFinsupp n (expo n t.1) := by
    intro s hs
    obtain ⟨t, ht, he⟩ := mem_support_toPoly hs
    rw [Finset.mem_image]
    exact ⟨t, List.mem_toFinset.2 ht, by rw [he, toFinsupp_ofFn]⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (List.toFinset_card_le _))

theorem le_card_support_ball (n : ℕ) (B : ℚ) :
    n ≤ (C B - ∑ i : Fin n, X i ^ 2 : MvPolynomial (Fin n) ℚ).support.card := by
  classical
  have hsub : (Finset.univ.image fun i : Fin n => Finsupp.single i 2) ⊆
      (C B - ∑ i : Fin n, X i ^ 2 : MvPolynomial (Fin n) ℚ).support := by
    intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
    rw [mem_support_iff, coeff_sub, coeff_C, coeff_sum]
    have : ∑ j : Fin n, ((X j ^ 2 : MvPolynomial (Fin n) ℚ)).coeff (Finsupp.single i 2) = 1 := by
      rw [Finset.sum_eq_single i]
      · simp [X_pow_eq_monomial, coeff_monomial]
      · intro j _ hj
        rw [X_pow_eq_monomial, coeff_monomial, ite_eq_right]
        intro h
        exact hj (Finsupp.single_left_injective (by norm_num) h)
      · simp
    rw [this, ite_eq_right (fun h => absurd (Finsupp.single_eq_zero.1 h.symm) (by norm_num))]
    norm_num
  have hinj : Function.Injective fun i : Fin n => Finsupp.single i 2 :=
    Finsupp.single_left_injective (by norm_num)
  calc n = (Finset.univ.image fun i : Fin n => Finsupp.single i 2).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    _ ≤ _ := Finset.card_le_card hsub

/-- **The number of variables of a valid problem** is at most its size: the explicit bound has a
term for each variable. -/
theorem numVars_le {P : Problem} (hP : P.Valid) : P.1 ≤ (encProblem P).length := by
  obtain ⟨-, -, -, ⟨B, hB⟩, -⟩ := hP
  obtain ⟨f, hf, hfB⟩ := List.mem_map.1 hB
  calc P.1 ≤ (f.toPoly P.1).support.card := by rw [hfB]; exact le_card_support_ball _ _
    _ ≤ f.length := card_support_toPoly_le _ _
    _ ≤ (encRaw f).length := length_le_encRaw f
    _ ≤ (encProblem P).length := length_encRaw_le_of_mem hf

/-! ### The budget -/

/-- The capped degrees of the constraints. -/
def degs (P : Problem) : List ℕ := P.2.2.1.map (degCap P.1 (P.2.1 + 1))

theorem degsSpec (P : Problem) : DegsSpec P.system P.2.1 (degs P) := by
  refine ⟨by simp [degs, Problem.system], fun i => ?_⟩
  have hi : (i : ℕ) < P.2.2.1.length := by simpa [Problem.system] using i.2
  rw [degs, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, degCap_eq,
    degree_eq_totalDegree]
  change _ = min (P.2.1 + 1) ((P.2.2.1.map (RawPoly.toPoly P.1))[(i : ℕ)]).totalDegree
  rw [List.getElem_map]

theorem budget_eq (P : Problem) (ηγ : ℚ × ℚ) :
    budget (P, ηγ) = ((encProblem P).length + 2) ^ (P.2.1 + 1) := rfl

theorem le_budget {P : Problem} (ηγ : ℚ × ℚ) {a : ℕ} (ha : a ≤ (encProblem P).length) (k : ℕ)
    (hk : k ≤ P.2.1 + 1) : (a + 1) ^ k ≤ budget (P, ηγ) := by
  rw [budget_eq]
  calc (a + 1) ^ k ≤ ((encProblem P).length + 2) ^ k := Nat.pow_le_pow_left (by omega) _
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hk

/-- **The budget is enough** for a valid problem. -/
theorem enough {P : Problem} (hP : P.Valid) (ηγ : ℚ × ℚ) :
    Enough (budget (P, ηγ)) P.1 (degs P).length P.2.1 := by
  refine ⟨?_, le_budget ηγ (numVars_le hP) _ (by omega),
    le_budget ηγ (by simpa [degs] using length_cons_le P) _ (by omega)⟩
  calc P.2.1 ≤ 2 ^ P.2.1 := (Nat.lt_two_pow_self).le
    _ = (1 + 1) ^ P.2.1 := by norm_num
    _ ≤ budget (P, ηγ) := le_budget (P := P) (a := 1) ηγ (by
        have := length_encProblem P
        omega) P.2.1 (by omega)

theorem numVars_le_budget {P : Problem} (hP : P.Valid) (ηγ : ℚ × ℚ) :
    P.1 ≤ budget (P, ηγ) :=
  calc P.1 ≤ (P.1 + 1) ^ 1 := by rw [pow_one]; omega
    _ ≤ budget (P, ηγ) := le_budget ηγ (numVars_le hP) 1 (by omega)

theorem length_pick (As : List RawPoly) {m : ℕ} (hm : m = As.length) (S : Finset (Fin m)) :
    (pick As (ind S)).length = S.card := by
  subst hm
  have hnd : ((List.range As.length).filter fun i => decide ((ind S).getD i 0 = 1)).Nodup :=
    List.nodup_range.filter _
  rw [pick, List.length_map, ← List.toFinset_card_of_nodup hnd, toFinset_filter_ind,
    Finset.card_map]

theorem mem_pick {As : List RawPoly} {v : List ℕ} {f : RawPoly} (hf : f ∈ pick As v) : f ∈ As := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf
  have hi' : i < As.length := List.mem_range.1 (List.mem_filter.1 hi).1
  rw [List.getD_eq_getElem _ _ hi']
  exact List.getElem_mem hi'

theorem card_le_of_mem_sets {σ K : Type*} [Field K] {A : System σ K} {ℓ : ℕ}
    {S : Finset (Fin A.length)} (hS : S ∈ sets A ℓ) : S.card ≤ ℓ := by
  classical
  unfold sets at hS
  obtain ⟨-, -, hnc, hdeg⟩ := Finset.mem_filter.1 hS
  rw [System.degree] at hdeg
  rw [Finset.card_eq_sum_ones]
  exact (Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.2 (hnc i hi)).trans hdeg

/-- **The products are within the budget.** -/
theorem prod_pick_le {P : Problem} (ηγ : ℚ × ℚ) :
    ∀ S ∈ sets (P.2.2.1.map (RawPoly.toPoly P.1)) P.2.1,
      ((pick P.2.2.1 (ind S)).map List.length).prod ≤ budget (P, ηγ) := by
  intro S hS
  have hlen : ∀ k ∈ (pick P.2.2.1 (ind S)).map List.length, k ≤ (encProblem P).length := by
    intro k hk
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hk
    exact (length_le_encRaw f).trans (length_encRaw_le_of_mem (mem_pick hf))
  calc ((pick P.2.2.1 (ind S)).map List.length).prod
      ≤ (encProblem P).length ^ ((pick P.2.2.1 (ind S)).map List.length).length :=
        List.prod_le_pow_length _ _ hlen
    _ ≤ ((encProblem P).length + 1) ^ P.2.1 := by
        rw [List.length_map, length_pick _ (by simp) S]
        calc (encProblem P).length ^ S.card ≤ ((encProblem P).length + 1) ^ S.card :=
              Nat.pow_le_pow_left (by omega) _
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (card_le_of_mem_sets hS)
    _ ≤ budget (P, ηγ) := le_budget ηγ le_rfl _ (by omega)

/-- **The context, for a valid problem**: nothing is cut. -/
theorem ctx_eq {P : Problem} (hP : P.Valid) (ηγ : ℚ × ℚ) :
    ctx ((P, ηγ), budget (P, ηγ)) = (P.1, coordsL P.1 P.2.1 (degs P), Mono.all P.1 (P.2.1 / 2),
      setData P.1 P.2.1 (degs P) (fun v => prodRaw P.1 (budget (P, ηγ)) (pick P.2.2.1 v))
        (fun v => ((pick P.2.2.1 v).map (normSq P.1)).prod),
      P.2.2.2.1, P.2.2.2.2, ηγ.1 + ηγ.2 / 2,
      1 / 2 ^ (16 * sizeZ (P, ηγ) (budget (P, ηγ)) ^ 4),
      2 ^ (3 * sizeZ (P, ηγ) (budget (P, ηγ)) ^ 2 + 1)) := by
  have he := enough hP ηγ
  have hn : min (budget (P, ηγ)) P.1 = P.1 := min_eq_right (numVars_le_budget hP ηγ)
  have hl : min (budget (P, ηγ)) P.2.1 = P.2.1 := min_eq_right he.deg
  have he' : Enough (budget (P, ηγ)) P.1 0 P.2.1 :=
    ⟨he.deg, he.vars, by simpa using (Nat.one_le_pow _ _ (Nat.succ_pos _)).trans he.vars⟩
  have hds : P.2.2.1.map (degCap P.1 (P.2.1 + 1)) = degs P := rfl
  simp only [ctx, hn, hl, hds]
  rw [coordsB_eq he, allB_eq_of_le he' (Nat.div_le_self _ _), setDataB_eq he]

/-! ### Sizes of numbers -/

theorem abs_le_two_pow_length (q : ℚ) : |(q : ℝ)| ≤ 2 ^ (encRat q).length := by
  have hlen : (encRat q).length = 2 * (q.num.natAbs.size + 1) + 1 +
      (Turing.MultiTapeTM.encNat q.den).length := by
    have : (encRat q).length =
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encIntBin Turing.MultiTapeTM.encNat
          (q.num, q.den)).length := rfl
    rw [this, Turing.MultiTapeTM.length_encPair, Turing.MultiTapeTM.length_encIntBin]
  have hnum : (q.num.natAbs : ℝ) < 2 ^ q.num.natAbs.size := by exact_mod_cast Nat.lt_size_self _
  have hq : |(q : ℝ)| ≤ q.num.natAbs := by
    have h1 : (q : ℝ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
    have h2 : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
    have h3 : |(q.num : ℝ)| = q.num.natAbs := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h1, abs_div, h3, abs_of_pos (by linarith : (0 : ℝ) < q.den)]
    exact div_le_self (by positivity) h2
  calc |(q : ℝ)| ≤ q.num.natAbs := hq
    _ ≤ 2 ^ q.num.natAbs.size := hnum.le
    _ ≤ 2 ^ (encRat q).length := pow_le_pow_right₀ (by norm_num) (by omega)

theorem one_le_length_encRat (q : ℚ) : 1 ≤ (encRat q).length := by
  have : (encRat q).length =
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encIntBin Turing.MultiTapeTM.encNat
        (q.num, q.den)).length := rfl
  rw [this, Turing.MultiTapeTM.length_encPair]
  omega

theorem den_le_two_pow_length (q : ℚ) : (q.den : ℝ) ≤ 2 ^ (encRat q).length := by
  have hlen : (Turing.MultiTapeTM.encNat q.den).length ≤ (encRat q).length := by
    have : (encRat q).length =
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encIntBin Turing.MultiTapeTM.encNat
          (q.num, q.den)).length := rfl
    rw [this, Turing.MultiTapeTM.length_encPair]
    dsimp only
    omega
  have h1 : (q.den : ℝ) < 2 ^ (Turing.MultiTapeTM.encNat q.den).length := by
    have : q.den < 2 ^ q.den.size := Nat.lt_size_self _
    have h2 : (Turing.MultiTapeTM.encNat q.den).length = q.den.size := by
      rw [Turing.MultiTapeTM.encNat_apply, Nat.size_eq_bits_len]
    rw [h2]
    exact_mod_cast this
  exact h1.le.trans (pow_le_pow_right₀ (by norm_num) hlen)

/-- A positive rational is at least `2^-|q|`. -/
theorem two_pow_inv_le {q : ℚ} (hq : 0 < q) : 1 / 2 ^ (encRat q).length ≤ (q : ℝ) := by
  have h1 : (q : ℝ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
  have hnum : (1 : ℝ) ≤ q.num := by exact_mod_cast Rat.num_pos.2 hq
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  rw [h1, div_le_div_iff₀ (by positivity) hd]
  calc 1 * (q.den : ℝ) ≤ 2 ^ (encRat q).length := by rw [one_mul]; exact den_le_two_pow_length q
    _ ≤ q.num * 2 ^ (encRat q).length := le_mul_of_one_le_left (by positivity) hnum

theorem sum_two_pow_le (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a) :
    (l.map fun a => (2 : ℝ) ^ a).sum ≤ 2 ^ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, pow_add]
    have ha := hl a List.mem_cons_self
    have h1 := ih fun b hb => hl b (List.mem_cons_of_mem _ hb)
    have h2 : (2 : ℝ) ≤ 2 ^ a := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha
    rcases eq_or_ne l [] with rfl | hne
    · simp
    · have h3 : (2 : ℝ) ≤ 2 ^ l.sum := by
        obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil l hne
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ l.sum := pow_le_pow_right₀ (by norm_num)
            ((hl b (List.mem_cons_of_mem _ hb)).trans (List.le_sum_of_mem hb))
      nlinarith

/-! ### Coefficient norms of raw polynomials -/

/-- The sum of the absolute values of the coefficients of the terms. -/
def rawNorm1 (p : RawPoly) : ℝ := (p.map fun t => |(t.2 : ℝ)|).sum

theorem rawNorm1_le (p : RawPoly) : rawNorm1 p ≤ 2 ^ (encRaw p).length := by
  have h1 : rawNorm1 p ≤ ((p.map fun t => (encRat t.2).length).map fun a => (2 : ℝ) ^ a).sum := by
    rw [rawNorm1, List.map_map]
    exact List.sum_le_sum fun t _ => abs_le_two_pow_length t.2
  refine h1.trans ((sum_two_pow_le _ fun a ha => ?_).trans (pow_le_pow_right₀ (by norm_num) ?_))
  · obtain ⟨t, -, rfl⟩ := List.mem_map.1 ha
    exact one_le_length_encRat _
  · calc (p.map fun t => (encRat t.2).length).sum ≤ (p.map fun t => (encTerm t).length).sum :=
          List.sum_le_sum fun t _ => by simp
      _ ≤ (encRaw p).length := Turing.MultiTapeTM.sum_length_le_length_encList encTerm p

theorem coeffNorm1_monomial {σ : Type*} (s : σ →₀ ℕ) (a : ℝ) :
    coeffNorm1 (monomial s a) = |a| := by
  classical
  by_cases ha : a = 0
  · simp [ha, coeffNorm1]
  · rw [coeffNorm1, support_monomial, ite_eq_right ha, Finset.sum_singleton, coeff_monomial,
      ite_eq_left rfl]

theorem coeffNorm1_list_sum_le {σ : Type*} (l : List (MvPolynomial σ ℝ)) :
    coeffNorm1 l.sum ≤ (l.map coeffNorm1).sum := by
  induction l with
  | nil => simp [coeffNorm1]
  | cons p l ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons]
    exact (coeffNorm1_add_le _ _).trans (add_le_add le_rfl ih)

theorem coeffNorm1_toReal_le (n : ℕ) (p : RawPoly) :
    coeffNorm1 (toReal (p.toPoly n)) ≤ rawNorm1 p := by
  rw [toReal_toPoly]
  refine (coeffNorm1_list_sum_le _).trans (le_of_eq ?_)
  rw [List.map_map, rawNorm1]
  congr 1
  exact List.map_congr_left fun t _ => by simp [coeffNorm1_monomial]

theorem coeffNorm_le_coeffNorm1 {σ : Type*} (p : MvPolynomial σ ℝ) :
    coeffNorm p ≤ coeffNorm1 p := by
  rw [coeffNorm, coeffNorm1]
  have hnn : ∀ m ∈ p.support, 0 ≤ |p.coeff m| := fun _ _ => abs_nonneg _
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg hnn, ?_⟩
  calc ∑ m ∈ p.support, p.coeff m ^ 2 = ∑ m ∈ p.support, |p.coeff m| * |p.coeff m| := by
        simp [sq, abs_mul_abs_self]
    _ ≤ ∑ m ∈ p.support, |p.coeff m| * ∑ m' ∈ p.support, |p.coeff m'| :=
        Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum hnn hm) (abs_nonneg _)
    _ = (∑ m ∈ p.support, |p.coeff m|) ^ 2 := by rw [← Finset.sum_mul, sq]

theorem denProd_le (l : List ℚ) :
    (Turing.MultiTapeTM.ComputableInPolyTime.denProd l : ℝ) ≤
      2 ^ (l.map fun q => (encRat q).length).sum := by
  induction l with
  | nil => simp [Turing.MultiTapeTM.ComputableInPolyTime.denProd]
  | cons q l ih =>
    have h : (Turing.MultiTapeTM.ComputableInPolyTime.denProd (q :: l) : ℝ) =
        q.den * Turing.MultiTapeTM.ComputableInPolyTime.denProd l := by
      simp [Turing.MultiTapeTM.ComputableInPolyTime.denProd]
    rw [h, List.map_cons, List.sum_cons, pow_add]
    exact mul_le_mul (den_le_two_pow_length q) ih (by exact_mod_cast
      (Turing.MultiTapeTM.ComputableInPolyTime.denProd_pos l).le) (by positivity)

theorem abs_coeff_le_coeffNorm {σ : Type*} (p : MvPolynomial σ ℝ) (s : σ →₀ ℕ) :
    |p.coeff s| ≤ coeffNorm p := by
  classical
  by_cases hs : s ∈ p.support
  · rw [coeffNorm, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun m => p.coeff m ^ 2)
      (fun _ _ => sq_nonneg _) hs)
  · rw [notMem_support_iff.1 hs, abs_zero]
    exact coeffNorm_nonneg p

/-- **A nonzero raw polynomial has a coefficient at least `2^-|p|`**, so its norm is at least
that. -/
theorem two_pow_inv_le_coeffNorm (n : ℕ) {p : RawPoly} (hp : p.toPoly n ≠ 0) :
    1 / 2 ^ (encRaw p).length ≤ coeffNorm (toReal (p.toPoly n)) := by
  classical
  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.1 hp
  set l := (p.filter fun t => expo n t.1 = List.ofFn s).map Prod.snd
  have hc : (p.toPoly n).coeff s = l.sum := by
    rw [← toFinsupp_ofFn s, coeff_toPoly p (by simp), coeff]
  -- The coefficient is an integer over the product of the denominators.
  have hsum := Turing.MultiTapeTM.ComputableInPolyTime.sum_eq_div_denProd l
  set D := Turing.MultiTapeTM.ComputableInPolyTime.denProd l
  set z := (l.map fun q => q.num * (D / q.den)).sum
  have hD : (0 : ℝ) < D := by exact_mod_cast Turing.MultiTapeTM.ComputableInPolyTime.denProd_pos l
  have hz : z ≠ 0 := by
    intro h0
    apply hs
    rw [hc, hsum, h0]
    simp
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hz
  have hlen : (l.map fun q => (encRat q).length).sum ≤ (encRaw p).length := by
    calc (l.map fun q => (encRat q).length).sum
        ≤ (p.map fun t => (encRat t.2).length).sum := by
          rw [List.map_map]
          exact (List.filter_sublist.map _).sum_le_sum (fun _ _ => Nat.zero_le _)
      _ ≤ (p.map fun t => (encTerm t).length).sum :=
          List.sum_le_sum fun t _ => by simp
      _ ≤ (encRaw p).length := Turing.MultiTapeTM.sum_length_le_length_encList encTerm p
  have hDle : (D : ℝ) ≤ 2 ^ (encRaw p).length :=
    (denProd_le l).trans (pow_le_pow_right₀ (by norm_num) hlen)
  have hcR : ((toReal (p.toPoly n)).coeff s) = (z : ℝ) / D := by
    rw [toReal, coeff_map, hc, hsum, eq_ratCast]
    push_cast
    rfl
  refine le_trans ?_ (abs_coeff_le_coeffNorm _ s)
  rw [hcR, abs_div, abs_of_pos hD, div_le_div_iff₀ (by positivity) hD]
  calc 1 * (D : ℝ) ≤ 2 ^ (encRaw p).length := by rw [one_mul]; exact hDle
    _ ≤ |(z : ℝ)| * 2 ^ (encRaw p).length := le_mul_of_one_le_left (by positivity) hz1

/-! ### Sizes for a valid problem -/

theorem sum_le_sum_cons (n : ℕ) (As : List RawPoly)
    (S : Finset (Fin (As.map (RawPoly.toPoly n)).length)) (g : RawPoly → ℕ) :
    ∑ i ∈ S, g (As.getD i []) ≤ (As.map g).sum := by
  calc ∑ i ∈ S, g (As.getD i []) ≤ ∑ i : Fin (As.map (RawPoly.toPoly n)).length, g (As.getD i []) :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    _ = (As.map g).sum := by
        rw [Coords.sum_map_getElem]
        refine Fintype.sum_equiv (finCongr (by simp)) _ _ fun i => ?_
        have hi : (i : ℕ) < As.length := by simpa using i.2
        simp [List.getElem?_eq_getElem hi]

/-- The constraints of a set are together no longer than the problem. -/
theorem sum_length_le (P : Problem) (S : Finset (Fin P.system.length)) :
    ∑ i ∈ S, (encRaw (P.2.2.1.getD i [])).length ≤ (encProblem P).length :=
  (sum_le_sum_cons P.1 P.2.2.1 S fun f => (encRaw f).length).trans
    ((Turing.MultiTapeTM.sum_length_le_length_encList encRaw _).trans (length_encList_cons_le P))

theorem coeffNorm1_prod_le {σ : Type*} {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    coeffNorm1 (∏ i ∈ s, f i) ≤ ∏ i ∈ s, coeffNorm1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [show (1 : MvPolynomial σ ℝ) = monomial 0 1 from rfl, coeffNorm1_monomial, abs_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (coeffNorm1_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (coeffNorm1_nonneg _))

theorem system_get (P : Problem) (i : Fin P.system.length) :
    P.system.get i = (P.2.2.1.getD i []).toPoly P.1 :=
  get_map_toPoly P.1 P.2.2.1 i

theorem coeffNorm1_get_le (P : Problem) (i : Fin P.system.length) :
    coeffNorm1 (toReal (P.system.get i)) ≤ 2 ^ (encRaw (P.2.2.1.getD i [])).length := by
  rw [system_get]
  exact (coeffNorm1_toReal_le _ _).trans (rawNorm1_le _)

/-- **The sizes of the products of constraints**: `‖∏ fᵢ‖₁ ≤ 2^|P|` and
`2^-|P| ≤ ∏ ‖fᵢ‖₂ ≤ 2^|P|` for every set of nonconstant constraints. -/
theorem prod_bounds (P : Problem) {S : Finset (Fin P.system.length)}
    (hS : ∀ i ∈ S, (P.system.get i).totalDegree ≠ 0) :
    coeffNorm1 (toReal (P.system.prod S)) ≤ 2 ^ (encProblem P).length ∧
      ∏ i ∈ S, coeffNorm (toReal (P.system.get i)) ≤ 2 ^ (encProblem P).length ∧
      1 / 2 ^ (encProblem P).length ≤ ∏ i ∈ S, coeffNorm (toReal (P.system.get i)) := by
  have hsum := sum_length_le P S
  have hpow : ∏ i ∈ S, (2 : ℝ) ^ (encRaw (P.2.2.1.getD i [])).length ≤
      2 ^ (encProblem P).length := by
    rw [Finset.prod_pow_eq_pow_sum]
    exact pow_le_pow_right₀ (by norm_num) hsum
  refine ⟨?_, ?_, ?_⟩
  · rw [System.prod, toReal_prod]
    refine (coeffNorm1_prod_le _ _).trans ((Finset.prod_le_prod₀ (fun _ _ => coeffNorm1_nonneg _)
      fun i _ => coeffNorm1_get_le P i).trans hpow)
  · exact (Finset.prod_le_prod₀ (fun _ _ => coeffNorm_nonneg _) fun i _ =>
      (coeffNorm_le_coeffNorm1 _).trans (coeffNorm1_get_le P i)).trans hpow
  · have hlow : ∀ i ∈ S, 1 / 2 ^ (encRaw (P.2.2.1.getD i [])).length ≤
        coeffNorm (toReal (P.system.get i)) := by
      intro i hi
      rw [system_get]
      refine two_pow_inv_le_coeffNorm _ fun h0 => hS i hi ?_
      rw [system_get, h0, totalDegree_zero]
    calc 1 / 2 ^ (encProblem P).length ≤ ∏ i ∈ S, 1 / (2 : ℝ) ^
          (encRaw (P.2.2.1.getD i [])).length := by
          rw [Finset.prod_div_distrib, Finset.prod_const_one]
          exact one_div_le_one_div_of_le (by positivity) hpow
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by positivity) hlow

/-- The objective polynomials have `‖q‖₁ ≤ 2^|q|`. -/
theorem coeffNorm1_obj_le {P : Problem} {q : RawPoly} (_hq : q ∈ P.2.2.2.1 :: P.2.2.2.2) :
    coeffNorm1 (toReal (q.toPoly P.1)) ≤ 2 ^ (encRaw q).length :=
  (coeffNorm1_toReal_le _ _).trans (rawNorm1_le _)

theorem sum_sq_obj_le (P : Problem) :
    ((P.2.2.2.2.map fun q => toReal (q.toPoly P.1)).map fun q => coeffNorm1 q ^ 2).sum ≤
      2 ^ (3 * (encProblem P).length) := by
  have h1 : ((P.2.2.2.2.map fun q => toReal (q.toPoly P.1)).map fun q => coeffNorm1 q ^ 2).sum ≤
      ((P.2.2.2.2.map fun q => 2 * (encRaw q).length + 1).map fun a => (2 : ℝ) ^ a).sum := by
    rw [List.map_map, List.map_map]
    refine List.sum_le_sum fun q hq => ?_
    simp only [Function.comp]
    have h := coeffNorm1_obj_le (P := P) (List.mem_cons_of_mem _ hq)
    calc coeffNorm1 (toReal (q.toPoly P.1)) ^ 2 ≤ (2 ^ (encRaw q).length) ^ 2 :=
          pow_le_pow_left₀ (coeffNorm1_nonneg _) h 2
      _ = 2 ^ (2 * (encRaw q).length) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (2 * (encRaw q).length + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  refine h1.trans ((sum_two_pow_le _ fun a ha => ?_).trans (pow_le_pow_right₀ (by norm_num) ?_))
  · obtain ⟨q, -, rfl⟩ := List.mem_map.1 ha
    omega
  · have h2 := Turing.MultiTapeTM.sum_length_le_length_encList encRaw P.2.2.2.2
    have h3 := length_le_encList encRaw P.2.2.2.2
    have h4 : (Turing.MultiTapeTM.encList encRaw P.2.2.2.2).length ≤ (encProblem P).length := by
      rw [length_encProblem]
      omega
    have h5 : (P.2.2.2.2.map fun q => 2 * (encRaw q).length + 1).sum =
        2 * (P.2.2.2.2.map fun q => (encRaw q).length).sum + P.2.2.2.2.length := by
      clear h1 h2 h3 h4
      induction P.2.2.2.2 with
      | nil => simp
      | cons q l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
    omega

/-! ### The run on a valid problem -/

section Run

variable (P : Problem) (η γ : ℚ)

/-- The size `Z`. -/
def Zof : ℕ := sizeZ (P, η, γ) (budget (P, η, γ))

/-- The coordinates. -/
def csOf : List Crd := coordsL P.1 P.2.1 (degs P)

/-- The dimension. -/
def Nof : ℕ := (csOf P).length

/-- The data of the sets. -/
def sdOf : List SetData := setData P.1 P.2.1 (degs P)
  (fun v => prodRaw P.1 (budget (P, η, γ)) (pick P.2.2.1 v))
  (fun v => ((pick P.2.2.1 v).map (normSq P.1)).prod)

/-- `τ`. -/
def τOf : ℚ := 1 / 2 ^ (16 * Zof P η γ ^ 4)

/-- `R`. -/
def ROf : ℚ := 2 ^ (3 * Zof P η γ ^ 2 + 1)

/-- The oracle. -/
def orcOf : List ℚ → Bool × List ℚ :=
  oracle P.1 (csOf P) (Mono.all P.1 (P.2.1 / 2)) (sdOf P η γ) P.2.2.2.1 P.2.2.2.2 (η + γ / 2)
    (τOf P η γ) (ROf P η γ)

/-- The objective. -/
def objOf : List ℚ → ℚ := objVal P.1 (csOf P) P.2.2.2.1 P.2.2.2.2

/-- The state after `k` steps. -/
def stOf (k : ℕ) : State :=
  run (Nof P) (expP (Zof P η γ) (Nof P)) (2 ^ expB (Zof P η γ) (Nof P)) (orcOf P η γ) (objOf P)
    (List.replicate (Nof P) 0) (shape₀ (Nof P) (2 ^ (8 * Zof P η γ ^ 2))) k

/-- The number of steps. -/
def Kof : ℕ := expK (Zof P η γ) (Nof P)

variable {P}

theorem finalState_eq (hP : P.Valid) :
    finalState ((P, η, γ), budget (P, η, γ)) = stOf P η γ (Kof P η γ) := by
  have h := ctx_eq hP (η, γ)
  simp only [finalState, stOf, Kof, Nof, csOf, ctxOracle, ctxObj, orcOf, objOf, sdOf, τOf, ROf,
    Zof, h]

theorem core_eq (hP : P.Valid) :
    core ((P, η, γ), budget (P, η, γ)) = outputL (budget (P, η, γ)) P.1 P.2.1 (csOf P)
      (if (stOf P η γ (Kof P η γ)).2.2.1 then (stOf P η γ (Kof P η γ)).2.2.2
        else List.replicate (Nof P) 0) (1 / 2 ^ (8 * Zof P η γ ^ 2)) := by
  have h := ctx_eq hP (η, γ)
  have hl : min (budget (P, η, γ)) P.2.1 = P.2.1 := min_eq_right (enough hP (η, γ)).deg
  rw [core, finalState_eq η γ hP]
  simp only [h, hl, Nof, csOf, Zof]

theorem stOf_succ (k : ℕ) : stOf P η γ (k + 1) =
    loopStep (Nof P) (expP (Zof P η γ) (Nof P)) (2 ^ expB (Zof P η γ) (Nof P)) (orcOf P η γ)
      (objOf P) (stOf P η γ k) := run_succ _ _ _ _ _ _ _ _

/-- The lengths along the run. -/
theorem lengths_stOf (k : ℕ) : (stOf P η γ k).1.length = Nof P ∧
    (stOf P η γ k).2.1.length = Nof P ∧ (∀ row ∈ (stOf P η γ k).2.1, row.length = Nof P) ∧
    (stOf P η γ k).2.2.2.length = Nof P := by
  induction k with
  | zero =>
    refine ⟨by simp [stOf, run], by simp [stOf, run, shape₀], fun row hrow => ?_,
      by simp [stOf, run]⟩
    simp only [stOf, run, Function.iterate_zero, id, shape₀, List.mem_map] at hrow
    obtain ⟨i, -, rfl⟩ := hrow
    simp
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [stOf_succ]
    simp only [loopStep]
    refine ⟨length_stepL_fst h1 h2, length_stepL_snd h2, length_row_stepL h2 h3, ?_⟩
    split_ifs
    · exact h1
    · exact h4

theorem matL_shape₀ (N : ℕ) (s : ℚ) :
    matL N (shape₀ N s) = (s : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  ext i j
  simp only [matL, shape₀, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, i.2, j.2,
    Option.map_some, Option.getD_some, Fin.ext_iff]
  split_ifs <;> simp

theorem vecL_replicate (N : ℕ) : vecL N (List.replicate N 0) = 0 := by
  ext i
  simp [vecL]

end Run

/-! ### The parameters

All parameters are powers of `2` in the size `Z ≥ 4`; these are the inequalities they satisfy. -/

section Parameters

theorem two_pow_le {a b : ℕ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) h

theorem two_pow_pos' (a : ℕ) : (0 : ℝ) < 2 ^ a := by positivity

/-- `x / 2^b ≤ y` from `x ≤ 2^a`, `2^c ≤ y`, `a ≤ b + c`. -/
theorem div_two_pow_le {x y : ℝ} {a b c : ℕ} (hx : x ≤ 2 ^ a) (hy : 2 ^ c ≤ y) (h : a ≤ b + c) :
    x / 2 ^ b ≤ y := by
  rw [div_le_iff₀ (two_pow_pos' b)]
  calc x ≤ 2 ^ a := hx
    _ ≤ 2 ^ (c + b) := two_pow_le (by omega)
    _ = 2 ^ c * 2 ^ b := pow_add _ _ _
    _ ≤ y * 2 ^ b := mul_le_mul_of_nonneg_right hy (by positivity)

/-- The box `R₀` of the lifted competitors. -/
theorem R₀_bound {Z : ℕ} (hZ : 4 ≤ Z) {Ry W F η : ℝ} (hRy : Ry ≤ 2 ^ (Z ^ 2)) (hRy0 : 0 ≤ Ry)
    (hW : W ≤ 2 ^ Z) (hF : F ≤ 2 ^ Z) (hF0 : 0 ≤ F) (hη : η ≤ 2 ^ Z) :
    Ry ≤ 2 ^ (3 * Z ^ 2) ∧ W * Ry + η * F ≤ 2 ^ (3 * Z ^ 2) := by
  refine ⟨hRy.trans (two_pow_le (by nlinarith)), ?_⟩
  have h1 : W * Ry ≤ 2 ^ (Z + Z ^ 2) := by
    rw [pow_add]
    exact mul_le_mul hW hRy hRy0 (by positivity)
  have h2 : η * F ≤ 2 ^ (Z + Z ^ 2) := by
    calc η * F ≤ 2 ^ Z * 2 ^ Z := mul_le_mul hη hF hF0 (by positivity)
      _ = 2 ^ (Z + Z) := (pow_add _ _ _).symm
      _ ≤ _ := two_pow_le (by nlinarith)
  calc W * Ry + η * F ≤ 2 ^ (Z + Z ^ 2) + 2 ^ (Z + Z ^ 2) := add_le_add h1 h2
    _ = 2 ^ (Z + Z ^ 2 + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ (3 * Z ^ 2) := two_pow_le (by nlinarith)


/-- `ρ (n + 1)^ℓ ≤ τ / 2`. -/
theorem ρ_bound₁ {Z : ℕ} (hZ : 4 ≤ Z) {c : ℝ} (hc : c ≤ 2 ^ Z) :
    1 / 2 ^ (32 * Z ^ 4) * c ≤ 1 / 2 ^ (16 * Z ^ 4) / 2 := by
  rw [div_div, one_div_mul_eq_div]
  rw [div_le_div_iff₀ (two_pow_pos' _) (by positivity)]
  calc c * (2 ^ (16 * Z ^ 4) * 2) ≤ 2 ^ Z * (2 ^ (16 * Z ^ 4) * 2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 2 ^ (Z + 16 * Z ^ 4 + 1) := by rw [pow_succ, pow_add]; ring
    _ ≤ 2 ^ (32 * Z ^ 4) := two_pow_le (by have := Nat.le_self_pow (by norm_num : 4 ≠ 0) Z; omega)
    _ = 1 * 2 ^ (32 * Z ^ 4) := (one_mul _).symm

/-- Comparing ratios of powers of `2`. -/
theorem two_pow_div_le {a b c d : ℕ} (h : a + d ≤ b + c) :
    (2 : ℝ) ^ a / 2 ^ b ≤ 2 ^ c / 2 ^ d := by
  rw [div_le_div_iff₀ (two_pow_pos' _) (two_pow_pos' _), ← pow_add, ← pow_add]
  exact two_pow_le (by omega)

theorem cast_le_two_pow (N : ℕ) : (N : ℝ) ≤ 2 ^ N := by
  exact_mod_cast (Nat.lt_two_pow_self).le

/-- The distance condition of the ball: `(n + 1)^ℓ (ρ (W + 1))² ≤ ((γ / 2) F)²`. -/
theorem ρ_bound₂ {Z : ℕ} (hZ : 4 ≤ Z) {c W F γ : ℝ} (hc : c ≤ 2 ^ Z)
    (hW : W ≤ 2 ^ Z) (hW0 : 0 ≤ W) (hF : 1 / 2 ^ Z ≤ F) (hγ : 1 / 2 ^ Z ≤ γ) :
    c * (1 / 2 ^ (32 * Z ^ 4) * (W + 1)) ^ 2 ≤ (γ / 2 * F) ^ 2 := by
  have h1 : W + 1 ≤ 2 ^ (Z + 1) := by
    have : (1 : ℝ) ≤ 2 ^ Z := one_le_pow₀ (by norm_num)
    rw [pow_succ]; linarith
  have h2 : 1 / 2 ^ (32 * Z ^ 4) * (W + 1) ≤ 2 ^ (Z + 1) / 2 ^ (32 * Z ^ 4) := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right h1 (by positivity)
  have h3 : c * (1 / 2 ^ (32 * Z ^ 4) * (W + 1)) ^ 2 ≤ 2 ^ (3 * Z + 2) / 2 ^ (64 * Z ^ 4) := by
    calc c * (1 / 2 ^ (32 * Z ^ 4) * (W + 1)) ^ 2
        ≤ 2 ^ Z * (2 ^ (Z + 1) / 2 ^ (32 * Z ^ 4)) ^ 2 :=
          mul_le_mul hc (pow_le_pow_left₀ (by positivity) h2 2) (by positivity) (by positivity)
      _ = 2 ^ (3 * Z + 2) / 2 ^ (64 * Z ^ 4) := by
          rw [div_pow, ← pow_mul, ← pow_mul, mul_div_assoc', ← pow_add]
          congr 2 <;> ring
  have h4 : (2 : ℝ) ^ (3 * Z + 2) / 2 ^ (64 * Z ^ 4) ≤ 2 ^ 0 / 2 ^ (4 * Z + 2) :=
    two_pow_div_le (by have := Nat.le_self_pow (by norm_num : 4 ≠ 0) Z; omega)
  have h5 : (2 : ℝ) ^ 0 / 2 ^ (4 * Z + 2) = (1 / 2 ^ (Z + 1) * (1 / 2 ^ Z)) ^ 2 := by
    rw [pow_zero, one_div_mul_one_div, ← pow_add, one_div_pow, ← pow_mul]
    congr 2; ring
  have h6 : 1 / 2 ^ (Z + 1) * (1 / 2 ^ Z) ≤ γ / 2 * F := by
    have : 1 / (2 : ℝ) ^ (Z + 1) ≤ γ / 2 := by
      rw [pow_succ, ← div_div]
      exact div_le_div_of_nonneg_right hγ (by norm_num)
    exact mul_le_mul this hF (by positivity)
      ((by positivity : (0 : ℝ) ≤ 1 / 2 ^ (Z + 1)).trans this)
  calc c * (1 / 2 ^ (32 * Z ^ 4) * (W + 1)) ^ 2 ≤ 2 ^ (3 * Z + 2) / 2 ^ (64 * Z ^ 4) := h3
    _ ≤ 2 ^ 0 / 2 ^ (4 * Z + 2) := h4
    _ = (1 / 2 ^ (Z + 1) * (1 / 2 ^ Z)) ^ 2 := h5
    _ ≤ (γ / 2 * F) ^ 2 := pow_le_pow_left₀ (by positivity) h6 2

/-- The objective changes by at most `γ / 2` on the ball. -/
theorem ρ_bound₃ {Z : ℕ} (hZ : 4 ≤ Z) {a b γ : ℝ} (ha : a ≤ 2 ^ Z) (hb : b ≤ 2 ^ (3 * Z))
    (hγ : 1 / 2 ^ Z ≤ γ) :
    1 / 2 ^ (32 * Z ^ 4) * (a + 2 * 2 ^ (3 * Z ^ 2 + 1) * b) ≤ γ / 2 := by
  have h1 : a + 2 * 2 ^ (3 * Z ^ 2 + 1) * b ≤ 2 ^ (3 * Z ^ 2 + 3 * Z + 3) := by
    have e1 : (2 : ℝ) ^ Z ≤ 2 ^ (3 * Z ^ 2 + 3 * Z + 2) := two_pow_le (by nlinarith)
    have e2 : 2 * (2 : ℝ) ^ (3 * Z ^ 2 + 1) * b ≤ 2 ^ (3 * Z ^ 2 + 3 * Z + 2) := by
      calc 2 * (2 : ℝ) ^ (3 * Z ^ 2 + 1) * b ≤ 2 * 2 ^ (3 * Z ^ 2 + 1) * 2 ^ (3 * Z) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = 2 ^ (3 * Z ^ 2 + 3 * Z + 2) := by rw [← pow_succ', ← pow_add]; ring_nf
    calc a + 2 * 2 ^ (3 * Z ^ 2 + 1) * b ≤ 2 ^ (3 * Z ^ 2 + 3 * Z + 2) +
          2 ^ (3 * Z ^ 2 + 3 * Z + 2) := add_le_add (ha.trans e1) e2
      _ = 2 ^ (3 * Z ^ 2 + 3 * Z + 3) := by rw [pow_succ]; ring
  have h2 : (1 : ℝ) / 2 ^ (Z + 1) ≤ γ / 2 := by
    rw [pow_succ, ← div_div]
    exact div_le_div_of_nonneg_right hγ (by norm_num)
  calc 1 / 2 ^ (32 * Z ^ 4) * (a + 2 * 2 ^ (3 * Z ^ 2 + 1) * b)
      ≤ 1 / 2 ^ (32 * Z ^ 4) * 2 ^ (3 * Z ^ 2 + 3 * Z + 3) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 ^ (3 * Z ^ 2 + 3 * Z + 3) / 2 ^ (32 * Z ^ 4) := one_div_mul_eq_div _ _
    _ ≤ 2 ^ 0 / 2 ^ (Z + 1) := two_pow_div_le (by
        have := Nat.le_self_pow (by norm_num : 4 ≠ 0) Z
        have : Z ^ 2 ≤ Z ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
        nlinarith)
    _ = 1 / 2 ^ (Z + 1) := by rw [pow_zero]
    _ ≤ γ / 2 := h2

/-- The starting ball contains the box: `N R² ≤ s`. -/
theorem ball_bound {Z N : ℕ} (hZ : 4 ≤ Z) (hN : N ≤ Z ^ 2) :
    (N : ℝ) * (2 ^ (3 * Z ^ 2 + 1)) ^ 2 ≤ 2 ^ (8 * Z ^ 2) := by
  calc (N : ℝ) * (2 ^ (3 * Z ^ 2 + 1)) ^ 2 ≤ 2 ^ (Z ^ 2) * 2 ^ (6 * Z ^ 2 + 2) := by
        rw [← pow_mul]
        refine mul_le_mul ((cast_le_two_pow N).trans (two_pow_le hN)) (le_of_eq (by ring_nf))
          (by positivity) (by positivity)
    _ = 2 ^ (7 * Z ^ 2 + 2) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (8 * Z ^ 2) := two_pow_le (by nlinarith)

/-- **Enough steps**: `(1/2)^J sᴺ < (ρ²)ᴺ`. -/
theorem det_bound {Z N : ℕ} (hN : 1 ≤ N) :
    (1 / 2 : ℝ) ^ (N * (64 * Z ^ 4 + 8 * Z ^ 2 + 1)) * (2 ^ (8 * Z ^ 2)) ^ N <
      ((1 / 2 ^ (32 * Z ^ 4)) ^ 2) ^ N := by
  rw [one_div_pow, ← pow_mul, one_div_pow, one_div_pow, ← pow_mul, ← pow_mul, one_div_mul_eq_div,
    div_lt_div_iff₀ (two_pow_pos' _) (two_pow_pos' _), one_mul, ← pow_add]
  exact pow_lt_pow_right₀ (by norm_num) (by nlinarith)

theorem pow_le_two_pow_mul (N k : ℕ) : (N : ℝ) ^ k ≤ 2 ^ (k * N) := by
  rw [mul_comm, pow_mul]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (cast_le_two_pow N) k

/-- **The rounding is fine enough.** -/
theorem δ_bounds {N K : ℕ} (hN : 1 ≤ N) {s : ℝ} (hs : 1 ≤ s) :
    (N : ℝ) * (2 / 2 ^ (2 * K + 3 * N + 16)) ≤ (1 / (4 * N)) ^ 2 * (s / 4 ^ K) / 8 ∧
      (N : ℝ) * (2 / 2 ^ (2 * K + 3 * N + 16)) ^ 2 ≤ (1 / (4 * N)) ^ 4 * (s / 4 ^ K) / 128 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h4 : (4 : ℝ) ^ K = 2 ^ (2 * K) := by rw [pow_mul]; norm_num
  have h3 := pow_le_two_pow_mul N 3
  have h5 := pow_le_two_pow_mul N 5
  constructor
  · have e : (1 / (4 * (N : ℝ))) ^ 2 * (s / 2 ^ (2 * K)) / 8 = s / (8 * (16 * N ^ 2 * 2 ^ (2 * K)))
        := by field_simp; ring
    rw [h4, e, le_div_iff₀ (by positivity), ← mul_assoc]
    calc (N : ℝ) * (2 / 2 ^ (2 * K + 3 * N + 16)) * 8 * (16 * N ^ 2 * 2 ^ (2 * K))
        = 256 * N ^ 3 * 2 ^ (2 * K) / 2 ^ (2 * K + 3 * N + 16) := by ring
      _ ≤ 2 ^ 8 * 2 ^ (3 * N) * 2 ^ (2 * K) / 2 ^ (2 * K + 3 * N + 16) := by
          gcongr; norm_num
      _ = 2 ^ (2 * K + 3 * N + 8) / 2 ^ (2 * K + 3 * N + 16) := by
          rw [← pow_add, ← pow_add]; ring_nf
      _ ≤ 1 := by
          rw [div_le_one (two_pow_pos' _)]
          exact two_pow_le (by omega)
      _ ≤ s := hs
  · have e : (1 / (4 * (N : ℝ))) ^ 4 * (s / 2 ^ (2 * K)) / 128 =
        s / (128 * (256 * N ^ 4 * 2 ^ (2 * K))) := by field_simp; ring
    rw [h4, e, le_div_iff₀ (by positivity), ← mul_assoc]
    calc (N : ℝ) * (2 / 2 ^ (2 * K + 3 * N + 16)) ^ 2 * 128 * (256 * N ^ 4 * 2 ^ (2 * K))
        = 2 ^ 17 * N ^ 5 * 2 ^ (2 * K) / (2 ^ (2 * K + 3 * N + 16)) ^ 2 := by
          rw [div_pow]; ring
      _ ≤ 2 ^ 17 * 2 ^ (5 * N) * 2 ^ (2 * K) / (2 ^ (2 * K + 3 * N + 16)) ^ 2 := by gcongr
      _ = 2 ^ (2 * K + 5 * N + 17) / 2 ^ (4 * K + 6 * N + 32) := by
          rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
      _ ≤ 1 := by
          rw [div_le_one (two_pow_pos' _)]
          exact two_pow_le (by omega)
      _ ≤ s := hs

/-- **The clamps never act**: the centers and shapes reachable in `K` steps stay below
`B = 2^(2K + 1) s`. -/
theorem clamp_bound {K k : ℕ} (hk : k < K) {s δ σ : ℝ} (hs : 1 ≤ s) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hσ : σ ≤ 1) :
    k * (Real.sqrt (2 ^ K * s) + δ) + σ * Real.sqrt (2 ^ k * s) + δ ≤ 2 ^ (2 * K + 1) * s ∧
      2 * (2 ^ k * s) + δ ≤ 2 ^ (2 * K + 1) * s := by
  have hK1 : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have hKs : 1 ≤ (2 : ℝ) ^ K * s := one_le_mul_of_one_le_of_one_le hK1 hs
  have hsq : Real.sqrt (2 ^ K * s) ≤ 2 ^ K * s := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hsqk : Real.sqrt (2 ^ k * s) ≤ Real.sqrt (2 ^ K * s) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (two_pow_le hk.le) (by linarith))
  have hKle : ((K : ℕ) : ℝ) + 1 ≤ 2 ^ K := by
    have := cast_le_two_pow K
    have h2 : (K : ℝ) + 1 ≤ 2 ^ K := by exact_mod_cast Nat.lt_two_pow_self
    exact h2
  have hk' : (k : ℝ) ≤ K := by exact_mod_cast hk.le
  have h2K : (2 : ℝ) ^ (2 * K + 1) * s = 2 * (2 ^ K * (2 ^ K * s)) := by
    rw [pow_succ, two_mul, pow_add]; ring
  constructor
  · have hsqrt0 := Real.sqrt_nonneg (2 ^ k * s)
    calc k * (Real.sqrt (2 ^ K * s) + δ) + σ * Real.sqrt (2 ^ k * s) + δ
        ≤ K * (2 ^ K * s + 1) + 1 * (2 ^ K * s) + 1 :=
          add_le_add (add_le_add (mul_le_mul hk' (add_le_add hsq hδ) (by positivity)
            (by positivity)) (mul_le_mul hσ (hsqk.trans hsq) hsqrt0 zero_le_one)) hδ
      _ = (K + 1) * (2 ^ K * s + 1) := by ring
      _ ≤ 2 ^ K * (2 ^ K * s + 1) := by gcongr
      _ ≤ 2 ^ K * (2 ^ K * s + 2 ^ K * s) := by gcongr
      _ = 2 ^ (2 * K + 1) * s := by rw [h2K]; ring
  · have h1 : (2 : ℝ) * 2 ^ k ≤ 2 ^ K := by
      rw [← pow_succ']; exact two_pow_le hk
    rw [h2K]
    nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ s)]

theorem interpBound_le (d : ℕ) : interpBound d ≤ (d + 1) ^ ((d + 1) ^ 2) := by
  unfold interpBound
  calc (d + 1).factorial * ((d + 1) ^ d) ^ (d + 1) ≤ (d + 1) ^ (d + 1) * ((d + 1) ^ d) ^ (d + 1) :=
        Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
    _ = (d + 1) ^ ((d + 1) ^ 2) := by rw [← pow_mul, ← pow_add]; ring_nf

/-- **The grid is well conditioned enough**: `τ ≤ t κ`. -/
theorem τ_bound {Z n d : ℕ} (hZ : 4 ≤ Z) (hn : n ≤ Z) (hd : d ≤ Z) :
    (1 / 2 ^ (16 * Z ^ 4) : ℝ) ≤ 1 / 2 ^ (8 * Z ^ 2) * (gridEig n d : ℝ) := by
  have hZ2 : Z + 1 ≤ 2 ^ Z := Nat.lt_two_pow_self
  have hden : (n + 1) ^ d * interpBound d ^ (2 * n) * (d + 1) ^ (2 * n) ≤
      2 ^ (16 * Z ^ 4 - 8 * Z ^ 2) := by
    have hd2 : d + 1 ≤ 2 ^ Z := (Nat.succ_le_succ hd).trans hZ2
    have hn2 : n + 1 ≤ 2 ^ Z := (Nat.succ_le_succ hn).trans hZ2
    have h2Z : 1 ≤ 2 ^ Z := Nat.one_le_two_pow
    have h1 : (n + 1) ^ d ≤ 2 ^ (Z * Z) :=
      calc (n + 1) ^ d ≤ (2 ^ Z) ^ d := Nat.pow_le_pow_left hn2 d
        _ ≤ (2 ^ Z) ^ Z := Nat.pow_le_pow_right (by positivity) hd
        _ = 2 ^ (Z * Z) := by rw [← pow_mul]
    have h2 : interpBound d ^ (2 * n) ≤ 2 ^ (Z * ((Z + 1) ^ 2 * (2 * Z))) :=
      calc interpBound d ^ (2 * n) ≤ ((d + 1) ^ ((d + 1) ^ 2)) ^ (2 * n) :=
            Nat.pow_le_pow_left (interpBound_le d) _
        _ ≤ ((2 ^ Z) ^ ((d + 1) ^ 2)) ^ (2 * n) :=
            Nat.pow_le_pow_left (Nat.pow_le_pow_left hd2 _) _
        _ ≤ ((2 ^ Z) ^ ((Z + 1) ^ 2)) ^ (2 * n) :=
            Nat.pow_le_pow_left (Nat.pow_le_pow_right (by positivity)
              (Nat.pow_le_pow_left (Nat.succ_le_succ hd) 2)) _
        _ ≤ ((2 ^ Z) ^ ((Z + 1) ^ 2)) ^ (2 * Z) :=
            Nat.pow_le_pow_right (by positivity) (by omega)
        _ = 2 ^ (Z * ((Z + 1) ^ 2 * (2 * Z))) := by rw [← pow_mul, ← pow_mul]
    have h3 : (d + 1) ^ (2 * n) ≤ 2 ^ (Z * (2 * Z)) :=
      calc (d + 1) ^ (2 * n) ≤ (2 ^ Z) ^ (2 * n) := Nat.pow_le_pow_left hd2 _
        _ ≤ (2 ^ Z) ^ (2 * Z) := Nat.pow_le_pow_right (by positivity) (by omega)
        _ = 2 ^ (Z * (2 * Z)) := by rw [← pow_mul]
    have a1 : 4 * Z ^ 2 ≤ Z ^ 3 :=
      calc 4 * Z ^ 2 ≤ Z * Z ^ 2 := Nat.mul_le_mul_right _ hZ
        _ = Z ^ 3 := by ring
    have a2 : 4 * Z ^ 3 ≤ Z ^ 4 :=
      calc 4 * Z ^ 3 ≤ Z * Z ^ 3 := Nat.mul_le_mul_right _ hZ
        _ = Z ^ 4 := by ring
    have h4 : Z * Z + Z * ((Z + 1) ^ 2 * (2 * Z)) + Z * (2 * Z) + 8 * Z ^ 2 ≤ 16 * Z ^ 4 := by
      ring_nf
      omega
    calc (n + 1) ^ d * interpBound d ^ (2 * n) * (d + 1) ^ (2 * n)
        ≤ 2 ^ (Z * Z) * 2 ^ (Z * ((Z + 1) ^ 2 * (2 * Z))) * 2 ^ (Z * (2 * Z)) := by gcongr
      _ = 2 ^ (Z * Z + Z * ((Z + 1) ^ 2 * (2 * Z)) + Z * (2 * Z)) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (16 * Z ^ 4 - 8 * Z ^ 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [gridEig]
  have hpos : 0 < (n + 1) ^ d * interpBound d ^ (2 * n) * (d + 1) ^ (2 * n) := by
    have : 0 < interpBound d := by unfold interpBound; positivity
    positivity
  push_cast
  rw [one_div_mul_one_div, one_div_le_one_div (by positivity)
    (mul_pos (by positivity) (by exact_mod_cast hpos))]
  have hcast : ((n + 1 : ℝ) ^ d * (interpBound d : ℝ) ^ (2 * n) * (d + 1 : ℝ) ^ (2 * n)) ≤
      2 ^ (16 * Z ^ 4 - 8 * Z ^ 2) := by exact_mod_cast hden
  calc (2 : ℝ) ^ (8 * Z ^ 2) * ((n + 1 : ℝ) ^ d * (interpBound d : ℝ) ^ (2 * n) *
        (d + 1 : ℝ) ^ (2 * n)) ≤ 2 ^ (8 * Z ^ 2) * 2 ^ (16 * Z ^ 4 - 8 * Z ^ 2) := by gcongr
    _ = 2 ^ (16 * Z ^ 4) := by
        rw [← pow_add]
        congr 1
        have h22 : Z ^ 2 ≤ Z ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
        omega

/-- The output's distance condition: `(n + 1)^ℓ (t (W + 1) Dμ)² ≤ ((γ - γ/2) F)²`. -/
theorem t_bound₁ {Z : ℕ} (hZ : 4 ≤ Z) {c W F γ D : ℝ} (hc : c ≤ 2 ^ Z) (hW : W ≤ 2 ^ Z)
    (hW0 : 0 ≤ W) (hD : D ≤ 2 ^ (Z ^ 2)) (hD0 : 0 ≤ D) (hF : 1 / 2 ^ Z ≤ F)
    (hγ : 1 / 2 ^ Z ≤ γ) :
    c * (1 / 2 ^ (8 * Z ^ 2) * ((W + 1) * D)) ^ 2 ≤ ((γ - γ / 2) * F) ^ 2 := by
  have h1 : (W + 1) * D ≤ 2 ^ (Z ^ 2 + Z + 1) := by
    have e : (1 : ℝ) ≤ 2 ^ Z := one_le_pow₀ (by norm_num)
    calc (W + 1) * D ≤ 2 ^ (Z + 1) * 2 ^ (Z ^ 2) :=
          mul_le_mul (by rw [pow_succ]; linarith) hD hD0 (by positivity)
      _ = 2 ^ (Z ^ 2 + Z + 1) := by rw [← pow_add]; ring_nf
  have h2 : 1 / 2 ^ (8 * Z ^ 2) * ((W + 1) * D) ≤ 2 ^ (Z ^ 2 + Z + 1) / 2 ^ (8 * Z ^ 2) := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right h1 (by positivity)
  have h3 : c * (1 / 2 ^ (8 * Z ^ 2) * ((W + 1) * D)) ^ 2 ≤
      2 ^ (2 * Z ^ 2 + 3 * Z + 2) / 2 ^ (16 * Z ^ 2) := by
    by_cases hc0 : c ≤ 0
    · calc c * (1 / 2 ^ (8 * Z ^ 2) * ((W + 1) * D)) ^ 2 ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hc0 (sq_nonneg _)
        _ ≤ _ := by positivity
    push Not at hc0
    calc c * (1 / 2 ^ (8 * Z ^ 2) * ((W + 1) * D)) ^ 2
        ≤ 2 ^ Z * (2 ^ (Z ^ 2 + Z + 1) / 2 ^ (8 * Z ^ 2)) ^ 2 :=
          mul_le_mul hc (pow_le_pow_left₀ (by positivity) h2 2) (by positivity) (by positivity)
      _ = 2 ^ (2 * Z ^ 2 + 3 * Z + 2) / 2 ^ (16 * Z ^ 2) := by
          rw [div_pow, ← pow_mul, ← pow_mul, mul_div_assoc', ← pow_add]
          congr 2 <;> ring
  have h4 : (2 : ℝ) ^ (2 * Z ^ 2 + 3 * Z + 2) / 2 ^ (16 * Z ^ 2) ≤ 2 ^ 0 / 2 ^ (4 * Z + 2) :=
    two_pow_div_le (by nlinarith)
  have h5 : (2 : ℝ) ^ 0 / 2 ^ (4 * Z + 2) = (1 / 2 ^ (Z + 1) * (1 / 2 ^ Z)) ^ 2 := by
    rw [pow_zero, one_div_mul_one_div, ← pow_add, one_div_pow, ← pow_mul]
    congr 2; ring
  have h6 : 1 / 2 ^ (Z + 1) * (1 / 2 ^ Z) ≤ (γ - γ / 2) * F := by
    have : 1 / (2 : ℝ) ^ (Z + 1) ≤ γ - γ / 2 := by
      rw [pow_succ, ← div_div, show γ - γ / 2 = γ / 2 by ring]
      exact div_le_div_of_nonneg_right hγ (by norm_num)
    exact mul_le_mul this hF (by positivity)
      ((by positivity : (0 : ℝ) ≤ 1 / 2 ^ (Z + 1)).trans this)
  calc c * (1 / 2 ^ (8 * Z ^ 2) * ((W + 1) * D)) ^ 2
      ≤ 2 ^ (2 * Z ^ 2 + 3 * Z + 2) / 2 ^ (16 * Z ^ 2) := h3
    _ ≤ 2 ^ 0 / 2 ^ (4 * Z + 2) := h4
    _ = (1 / 2 ^ (Z + 1) * (1 / 2 ^ Z)) ^ 2 := h5
    _ ≤ ((γ - γ / 2) * F) ^ 2 := pow_le_pow_left₀ (by positivity) h6 2

/-- Mixing in the grid moves the objective by at most `γ / 2`. -/
theorem t_bound₂ {Z : ℕ} (hZ : 4 ≤ Z) {a b γ D : ℝ} (ha : a ≤ 2 ^ Z) (hb : b ≤ 2 ^ (3 * Z))
    (hD : D ≤ 2 ^ (Z ^ 2)) (hD0 : 0 ≤ D) (hγ : 1 / 2 ^ Z ≤ γ) :
    1 / 2 ^ (8 * Z ^ 2) * (2 ^ (3 * Z ^ 2 + 1) + D) *
      (a + 2 * (2 ^ (3 * Z ^ 2 + 1) + D) * b) ≤ γ / 2 := by
  have hRD : (2 : ℝ) ^ (3 * Z ^ 2 + 1) + D ≤ 2 ^ (3 * Z ^ 2 + 2) := by
    have : (2 : ℝ) ^ (Z ^ 2) ≤ 2 ^ (3 * Z ^ 2 + 1) := two_pow_le (by nlinarith)
    rw [pow_succ 2 (3 * Z ^ 2 + 1)]; linarith
  have hRD0 : (0 : ℝ) ≤ 2 ^ (3 * Z ^ 2 + 1) + D := by positivity
  have h1 : a + 2 * (2 ^ (3 * Z ^ 2 + 1) + D) * b ≤ 2 ^ (3 * Z ^ 2 + 3 * Z + 4) := by
    have e1 : (2 : ℝ) ^ Z ≤ 2 ^ (3 * Z ^ 2 + 3 * Z + 3) := two_pow_le (by nlinarith)
    have e2 : 2 * ((2 : ℝ) ^ (3 * Z ^ 2 + 1) + D) * b ≤ 2 ^ (3 * Z ^ 2 + 3 * Z + 3) := by
      by_cases hb0 : b ≤ 0
      · calc 2 * ((2 : ℝ) ^ (3 * Z ^ 2 + 1) + D) * b ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by positivity) hb0
          _ ≤ _ := by positivity
      push Not at hb0
      calc 2 * ((2 : ℝ) ^ (3 * Z ^ 2 + 1) + D) * b ≤ 2 * 2 ^ (3 * Z ^ 2 + 2) * 2 ^ (3 * Z) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hRD (by norm_num)) hb hb0.le (by positivity)
        _ = 2 ^ (3 * Z ^ 2 + 3 * Z + 3) := by rw [← pow_succ', ← pow_add]; ring_nf
    calc a + 2 * (2 ^ (3 * Z ^ 2 + 1) + D) * b ≤ 2 ^ (3 * Z ^ 2 + 3 * Z + 3) +
          2 ^ (3 * Z ^ 2 + 3 * Z + 3) := add_le_add (ha.trans e1) e2
      _ = 2 ^ (3 * Z ^ 2 + 3 * Z + 4) := by rw [pow_succ]; ring
  have h2 : (1 : ℝ) / 2 ^ (Z + 1) ≤ γ / 2 := by
    rw [pow_succ, ← div_div]
    exact div_le_div_of_nonneg_right hγ (by norm_num)
  by_cases hneg : a + 2 * (2 ^ (3 * Z ^ 2 + 1) + D) * b ≤ 0
  · calc 1 / 2 ^ (8 * Z ^ 2) * (2 ^ (3 * Z ^ 2 + 1) + D) * (a + 2 * (2 ^ (3 * Z ^ 2 + 1) + D) * b)
        ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
      _ ≤ 1 / 2 ^ (Z + 1) := by positivity
      _ ≤ γ / 2 := h2
  push Not at hneg
  calc 1 / 2 ^ (8 * Z ^ 2) * (2 ^ (3 * Z ^ 2 + 1) + D) * (a + 2 * (2 ^ (3 * Z ^ 2 + 1) + D) * b)
      ≤ 1 / 2 ^ (8 * Z ^ 2) * 2 ^ (3 * Z ^ 2 + 2) * 2 ^ (3 * Z ^ 2 + 3 * Z + 4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hRD (by positivity)) h1 hneg.le (by positivity)
    _ = 2 ^ (6 * Z ^ 2 + 3 * Z + 6) / 2 ^ (8 * Z ^ 2) := by
        rw [one_div_mul_eq_div, div_mul_eq_mul_div, ← pow_add]; ring_nf
    _ ≤ 2 ^ 0 / 2 ^ (Z + 1) := two_pow_div_le (by nlinarith)
    _ = 1 / 2 ^ (Z + 1) := by rw [pow_zero]
    _ ≤ γ / 2 := h2

end Parameters

/-! ### The size `Z` of a valid input -/

section Sizes

variable {P : Problem} {η γ : ℚ}

theorem length_encInput (P : Problem) (η γ : ℚ) : (encInput (P, η, γ)).length =
    2 * (encProblem P).length + 1 + (2 * (encRat η).length + 1 + (encRat γ).length) := by
  rw [SoS.PolyTime.encInput_apply]
  simp only [SoS.PolyTime.encInputM, Turing.MultiTapeTM.length_encPair]
  rw [length_encProblem]

theorem Zof_eq (P : Problem) (η γ : ℚ) :
    Zof P η γ = (encInput (P, η, γ)).length + budget (P, η, γ) + 4 := rfl

theorem four_le_Zof : 4 ≤ Zof P η γ := by rw [Zof_eq]; omega

theorem lenP_le_Zof : (encProblem P).length ≤ Zof P η γ := by
  rw [Zof_eq, length_encInput]; omega

theorem budget_le_Zof : budget (P, η, γ) + 4 ≤ Zof P η γ := by rw [Zof_eq]; omega

theorem η_le_Zof : (η : ℝ) ≤ 2 ^ Zof P η γ := by
  refine (le_abs_self _).trans ((abs_le_two_pow_length η).trans (two_pow_le ?_))
  rw [Zof_eq, length_encInput]; omega

theorem γ_ge_Zof (hγ : 0 < γ) : 1 / 2 ^ Zof P η γ ≤ (γ : ℝ) := by
  refine le_trans ?_ (two_pow_inv_le hγ)
  refine one_div_le_one_div_of_le (two_pow_pos' _) (two_pow_le ?_)
  rw [Zof_eq, length_encInput]; omega

/-- The number of coordinates. -/
theorem length_coordsL_le (n ℓ : ℕ) (ds : List ℕ) :
    (coordsL n ℓ ds).length ≤ (n + 1) ^ ℓ * (1 + (ds.length + 1) ^ ℓ) := by
  have hall : ∀ D ≤ ℓ, (Mono.all n D).length ≤ (n + 1) ^ ℓ := fun D hD =>
    (Mono.length_all_le n D).trans (Nat.pow_le_pow_right (by omega) hD)
  rw [coordsL, List.length_append, List.length_map, List.length_flatMap]
  have h1 : ((Mono.all n ℓ).filter fun e => decide (e.sum ≠ 0)).length ≤ (n + 1) ^ ℓ :=
    (List.length_filter_le _ _).trans (hall ℓ le_rfl)
  have h2 : ((setsL ℓ ds).map fun v => ((Mono.all n (ℓ - dsum ds v)).map
      fun e => ((some v, e) : Crd)).length).sum ≤ (setsL ℓ ds).length * (n + 1) ^ ℓ := by
    have := List.sum_le_length_nsmul ((setsL ℓ ds).map fun v => ((Mono.all n (ℓ - dsum ds v)).map
      fun e => ((some v, e) : Crd)).length) ((n + 1) ^ ℓ) fun k hk => by
        obtain ⟨v, -, rfl⟩ := List.mem_map.1 hk
        rw [List.length_map]
        exact hall _ (Nat.sub_le _ _)
    simpa using this
  have h3 : (setsL ℓ ds).length ≤ (ds.length + 1) ^ ℓ :=
    (List.length_filter_le _ _).trans (Mono.length_all_le _ _)
  calc _ ≤ (n + 1) ^ ℓ + (setsL ℓ ds).length * (n + 1) ^ ℓ := add_le_add h1 h2
    _ ≤ (n + 1) ^ ℓ + (ds.length + 1) ^ ℓ * (n + 1) ^ ℓ := by gcongr
    _ = _ := by ring

theorem Nof_le (hP : P.Valid) : Nof P ≤ Zof P η γ ^ 2 := by
  have he := enough hP (η, γ)
  have hL := budget_le_Zof (P := P) (η := η) (γ := γ)
  have h := length_coordsL_le P.1 P.2.1 (degs P)
  rw [Nof, csOf]
  calc _ ≤ (P.1 + 1) ^ P.2.1 * (1 + ((degs P).length + 1) ^ P.2.1) := h
    _ ≤ budget (P, η, γ) * (1 + budget (P, η, γ)) := by gcongr <;> [exact he.vars; exact he.cons]
    _ ≤ Zof P η γ * Zof P η γ := by gcongr <;> omega
    _ = _ := by ring

end Sizes

/-! ### The ellipsoid method on the run -/

section Main

open Matrix

variable {P : Problem} {η γ : ℚ}

theorem length_orDef (a : List ℚ) : (orDef a).length = a.length := by
  unfold orDef
  split_ifs <;> simp [unitVec]

theorem length_of_mem_cuts {n : ℕ} {cs : List Crd} {msY : List (List ℕ)} {sd : List SetData}
    {η τ R : ℚ} {c a : List ℚ} (hc : c.length = cs.length)
    (ha : a ∈ cuts n cs msY sd η τ R c) : a.length = cs.length := by
  simp only [cuts, List.mem_append, List.mem_flatMap] at ha
  rcases ha with ((ha | ha) | ⟨d, -, ha⟩) | ⟨d, -, ha⟩
  · obtain ⟨p, -, rfl⟩ := List.mem_map.1 ha
    simp [unitVec, hc]
  · unfold psdYCuts at ha
    cases hw : PDTestRat.test (momRows n (yv cs c) τ msY) with
    | none => rw [hw] at ha; simp at ha
    | some w =>
      rw [hw] at ha
      simp only [Option.elim, List.mem_singleton] at ha
      rw [ha, length_orDef, length_dense]
  · unfold psdWCuts at ha
    cases hw : PDTestRat.test (momRows n (wv cs c d.1) τ d.2.1) with
    | none => rw [hw] at ha; simp at ha
    | some w =>
      rw [hw] at ha
      simp only [Option.elim, List.mem_singleton] at ha
      rw [ha, length_orDef, length_dense]
  · unfold distCuts at ha
    split_ifs at ha
    · rw [List.mem_singleton.1 ha, length_orDef, length_dense]
    · simp at ha

theorem length_orcOf {c : List ℚ} (hc : c.length = Nof P) : (orcOf P η γ c).2.length = Nof P := by
  unfold orcOf oracle
  split_ifs with hempty
  · rw [length_orDef, length_dense]; rfl
  · rw [List.isEmpty_iff] at hempty
    obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil hempty
    simp only [hl, List.headD_cons]
    exact length_of_mem_cuts hc (by rw [hl]; exact List.mem_cons_self)

theorem dotProduct_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (u v : κ → ℝ) :
    (u ∘ e) ⬝ᵥ (v ∘ e) = u ⬝ᵥ v := by
  simp only [dotProduct, Function.comp]
  exact Equiv.sum_comp e fun j => u j * v j

theorem abs_coeff_le_coeffNorm1 {σ : Type*} (p : MvPolynomial σ ℝ) (s : σ →₀ ℕ) :
    |p.coeff s| ≤ coeffNorm1 p := by
  classical
  by_cases hs : s ∈ p.support
  · exact Finset.single_le_sum (f := fun m => |p.coeff m|) (fun _ _ => abs_nonneg _) hs
  · rw [notMem_support_iff.1 hs, abs_zero]
    exact coeffNorm1_nonneg p

/-- **The moments of a competitor** are at most `2^(Z²)`. -/
theorem moment_bound (hP : P.Valid) (hη : 0 ≤ (η : ℝ))
    (E' : PseudoExpectation (Fin P.1) P.2.1) (hE' : E'.ApproxSatisfies P.system (η : ℝ) 0)
    (m : Fin P.1 →₀ ℕ) (hm : m.degree ≤ P.2.1) :
    |E' (monomial m 1)| ≤ 2 ^ (Zof P η γ ^ 2) := by
  obtain ⟨hev, -, -, ⟨B, hB⟩, -⟩ := id hP
  have h := PseudoExpectation.abs_apply_monomial_le hev E' hη hE' hB hm
  obtain ⟨f, hf, hfB⟩ := List.mem_map.1 hB
  set g : MvPolynomial (Fin P.1) ℚ := C B - ∑ i, X i ^ 2
  have hg1 : coeffNorm1 (toReal g) ≤ 2 ^ (encProblem P).length := by
    rw [← hfB]
    exact (coeffNorm1_toReal_le _ _).trans ((rawNorm1_le f).trans
      (two_pow_le (length_encRaw_le_of_mem hf)))
  have hB' : |algebraMap ℚ ℝ B| ≤ 2 ^ (encProblem P).length := by
    have hc : (toReal g).coeff 0 = algebraMap ℚ ℝ B := by
      simp only [g, toReal, coeff_map, coeff_sub, coeff_C, coeff_sum]
      rw [Finset.sum_eq_zero fun i _ => by
        rw [X_pow_eq_monomial, coeff_monomial, ite_eq_right (fun h0 => by
          have := congrArg (fun f => f i) h0
          simp at this)]]
      simp
    rw [← hc]
    exact (abs_coeff_le_coeffNorm1 _ _).trans hg1
  have hnorm : coeffNorm (toReal g) ≤ 2 ^ (encProblem P).length :=
    (coeffNorm_le_coeffNorm1 _).trans hg1
  have hηle : (η : ℝ) ≤ 2 ^ (encRat η).length := (le_abs_self _).trans (abs_le_two_pow_length η)
  have hlen : (encProblem P).length + (encRat η).length + 2 ≤ Zof P η γ := by
    rw [Zof_eq, length_encInput]; omega
  have hℓ : P.2.1 / 2 ≤ Zof P η γ := by
    have := budget_le_Zof (P := P) (η := η) (γ := γ)
    have := (enough hP (η, γ)).deg
    omega
  have hbase : 1 + |algebraMap ℚ ℝ B| + (η : ℝ) * coeffNorm (toReal g) ≤ 2 ^ Zof P η γ := by
    calc 1 + |algebraMap ℚ ℝ B| + (η : ℝ) * coeffNorm (toReal g)
        ≤ 2 ^ (encProblem P).length + 2 ^ (encProblem P).length +
            2 ^ (encRat η).length * 2 ^ (encProblem P).length :=
          add_le_add (add_le_add (one_le_pow₀ (by norm_num)) hB')
            (mul_le_mul hηle hnorm (coeffNorm_nonneg _) (by positivity))
      _ ≤ 2 ^ ((encProblem P).length + (encRat η).length + 2) := by
          have e1 : (2 : ℝ) ^ (encProblem P).length ≤
              2 ^ ((encProblem P).length + (encRat η).length) := two_pow_le (by omega)
          have e2 : (2 : ℝ) ^ (encRat η).length * 2 ^ (encProblem P).length =
              2 ^ ((encProblem P).length + (encRat η).length) := by rw [← pow_add, add_comm]
          rw [pow_add 2 _ 2, e2, show (2 : ℝ) ^ 2 = 4 by norm_num]
          have e3 : (0 : ℝ) ≤ 2 ^ ((encProblem P).length + (encRat η).length) := by positivity
          linarith
      _ ≤ 2 ^ Zof P η γ := two_pow_le hlen
  calc |E' (monomial m 1)| ≤ _ := h
    _ ≤ (2 ^ Zof P η γ) ^ (P.2.1 / 2) :=
        pow_le_pow_left₀ (add_nonneg (add_nonneg zero_le_one (abs_nonneg _))
          (mul_nonneg hη (coeffNorm_nonneg _))) hbase _
    _ ≤ (2 ^ Zof P η γ) ^ Zof P η γ := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hℓ
    _ = 2 ^ (Zof P η γ ^ 2) := by rw [← pow_mul, sq]

/-- The set the cuts keep. -/
def CSet (P : Problem) (η γ : ℚ) : Set (Fin (Nof P) → ℝ) :=
  {x | InSet P.system P.2.1 ((η + γ / 2 : ℚ) : ℝ) ((τOf P η γ : ℝ) / 2) (ROf P η γ)
    (x ∘ equiv (degsSpec P))}

/-- The objective on the coordinates. -/
noncomputable def fObj (P : Problem) (x : Fin (Nof P) → ℝ) : ℝ :=
  obj (toReal (P.2.2.2.1.toPoly P.1)) (P.2.2.2.2.map fun q => toReal (q.toPoly P.1))
    (ys (x ∘ equiv (degsSpec P)))

theorem pt_eq (P : Problem) (l : List ℚ) :
    pt (degsSpec P) l = vecL (Nof P) l ∘ equiv (degsSpec P) :=
  rfl

theorem fObj_vecL (P : Problem) (l : List ℚ) : fObj P (vecL (Nof P) l) = (objOf P l : ℝ) := by
  rw [fObj, ← pt_eq, objOf, obj_pt]
  rfl

theorem setDataSpec_of :
    SetDataSpec P.system P.2.1 (fun v => prodRaw P.1 (budget (P, η, γ)) (pick P.2.2.1 v))
      (fun v => ((pick P.2.2.1 v).map (normSq P.1)).prod) :=
  setDataSpec P.1 P.2.1 _ P.2.2.1 (prod_pick_le (η, γ))

/-- **The oracle on the run**, from `SoS.Oracle.oracle_spec`. -/
theorem orc_spec (hP : P.Valid) (hN : 0 < Nof P) (k : ℕ) :
    let r := orcOf P η γ (stOf P η γ k).1
    vecL (Nof P) r.2 ≠ 0 ∧
      (r.1 = false → ∀ x ∈ CSet P η γ,
        vecL (Nof P) r.2 ⬝ᵥ (x - vecL (Nof P) (stOf P η γ k).1) ≤ 0) ∧
      (r.1 = true → InSet P.system P.2.1 ((η + γ / 2 : ℚ) : ℝ) (τOf P η γ) (ROf P η γ)
          (pt (degsSpec P) (stOf P η γ k).1) ∧
        ∀ x ∈ Set.univ, fObj P x < fObj P (vecL (Nof P) (stOf P η γ k).1) →
          vecL (Nof P) r.2 ⬝ᵥ (x - vecL (Nof P) (stOf P η γ k).1) ≤ 0) := by
  intro r
  have hτ : (0 : ℚ) < τOf P η γ := by unfold τOf; positivity
  have h := oracle_spec (degsSpec P) (setDataSpec_of (P := P) (η := η) (γ := γ)) hP.2.2.1 hτ
    (η := η + γ / 2) (R := ROf P η γ) (c := (stOf P η γ k).1) (lengths_stOf η γ k).1 hN
  obtain ⟨h1, h2, h3⟩ := h
  have hdot : ∀ x : Fin (Nof P) → ℝ, vecL (Nof P) r.2 ⬝ᵥ (x - vecL (Nof P) (stOf P η γ k).1) =
      pt (degsSpec P) r.2 ⬝ᵥ (x ∘ equiv (degsSpec P) - pt (degsSpec P) (stOf P η γ k).1) := by
    intro x
    rw [pt_eq, pt_eq]
    simp only [dotProduct, Function.comp, Pi.sub_apply]
    exact (Equiv.sum_comp (equiv (degsSpec P)) (fun j => vecL (Nof P) r.2 j *
      (x j - vecL (Nof P) (stOf P η γ k).1 j))).symm
  refine ⟨fun h0 => h1 (by
    rw [pt_eq]
    change vecL (Nof P) r.2 ∘ equiv (degsSpec P) = 0
    rw [h0]
    rfl), fun hf x hx => ?_, fun ht => ⟨(h3 ht).1, ?_⟩⟩
  · rw [hdot]
    exact h2 hf _ hx
  · intro x _ hlt
    rw [hdot]
    refine (h3 ht).2 _ ?_
    rw [fObj, fObj] at hlt
    exact hlt

theorem abs_ys_sub_le {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K] {A : System σ K}
    {ℓ : ℕ} {x x' : Coord A ℓ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hnear : ∀ i, |x i - x' i| ≤ ρ)
    (m : σ →₀ ℕ) : |ys x m - ys x' m| ≤ ρ := by
  unfold ys
  split_ifs
  · exact hnear _
  all_goals simpa using hρ

theorem τOf_cast (P : Problem) (η γ : ℚ) : (τOf P η γ : ℝ) = 1 / 2 ^ (16 * Zof P η γ ^ 4) := by
  simp [τOf]

theorem ROf_cast (P : Problem) (η γ : ℚ) : (ROf P η γ : ℝ) = 2 ^ (3 * Zof P η γ ^ 2 + 1) := by
  simp [ROf]

theorem numVars_pow_le (hP : P.Valid) :
    ((Fintype.card (Fin P.1) : ℝ) + 1) ^ P.2.1 ≤ 2 ^ Zof P η γ := by
  have he := (enough hP (η, γ)).vars
  have hL := budget_le_Zof (P := P) (η := η) (γ := γ)
  have h1 : (P.1 + 1) ^ P.2.1 ≤ Zof P η γ := by omega
  rw [Fintype.card_fin]
  calc ((P.1 : ℝ) + 1) ^ P.2.1 = (((P.1 + 1) ^ P.2.1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (Zof P η γ : ℝ) := by exact_mod_cast h1
    _ ≤ 2 ^ Zof P η γ := cast_le_two_pow _

theorem objective_eq (E' : PseudoExpectation (Fin P.1) P.2.1) :
    P.objective E' = E' (toReal (P.2.2.2.1.toPoly P.1)) +
      ((P.2.2.2.2.map fun q => toReal (q.toPoly P.1)).map fun q => E' q ^ 2).sum := by
  rw [Problem.objective, List.map_map]
  rfl

/-- **A ball around every competitor.** -/
theorem ball_ok (hP : P.Valid) (hη : 0 < η) (hγ : 0 < γ)
    (E' : PseudoExpectation (Fin P.1) P.2.1) (hE' : E'.ApproxSatisfies P.system (η : ℝ) 0) :
    ∃ z : Fin (Nof P) → ℝ, ∀ x, (x - z) ⬝ᵥ (x - z) ≤ (1 / 2 ^ (32 * Zof P η γ ^ 4)) ^ 2 →
      x ∈ CSet P η γ ∧ fObj P x ≤ P.objective E' + γ / 2 := by
  classical
  have hZ : 4 ≤ Zof P η γ := four_le_Zof
  have hη0 : (0 : ℝ) ≤ η := by exact_mod_cast hη.le
  have hγ0 : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hlenP := lenP_le_Zof (P := P) (η := η) (γ := γ)
  have hq : ∀ q ∈ toReal (P.2.2.2.1.toPoly P.1) :: P.2.2.2.2.map fun q => toReal (q.toPoly P.1),
      q.totalDegree ≤ P.2.1 := by
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact (totalDegree_toReal_le _).trans (hP.2.2.1 _ List.mem_cons_self)
    · obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      exact (totalDegree_toReal_le _).trans (hP.2.2.1 _ (List.mem_cons_of_mem _ hq'))
  -- The bounds of the sets of constraints.
  have hsets : ∀ S ∈ sets P.system P.2.1, ∀ i ∈ S, (P.system.get i).totalDegree ≠ 0 :=
    fun S hS => (Finset.mem_filter.1 hS).2.2.1
  have hW : ∀ S ∈ sets P.system P.2.1, coeffNorm1 (toReal (P.system.prod S)) ≤
      2 ^ (encProblem P).length := fun S hS => (prod_bounds P (hsets S hS)).1
  have hF : ∀ S ∈ sets P.system P.2.1, ∏ i ∈ S, coeffNorm (toReal (P.system.get i)) ≤
      2 ^ (encProblem P).length := fun S hS => (prod_bounds P (hsets S hS)).2.1
  have hR₀ := R₀_bound hZ (Ry := 2 ^ (Zof P η γ ^ 2)) le_rfl (by positivity)
    ((two_pow_le hlenP)) ((two_pow_le hlenP)) (by positivity) (η_le_Zof (P := P) (γ := γ))
  obtain ⟨zC, hzC, hagree⟩ := exists_lift E' hη0 hE'
    (fun m hm => moment_bound (γ := γ) hP hη0 E' hE' m hm) hW hF hR₀.1 hR₀.2
  set e := equiv (degsSpec P)
  set ρ : ℝ := 1 / 2 ^ (32 * Zof P η γ ^ 4)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    simp only [ρ]
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  set z : Fin (Nof P) → ℝ := fun j => zC (e.symm j)
  refine ⟨z, fun x hx => ?_⟩
  -- Coordinate by coordinate, `x` is within `ρ` of the lift.
  have hnear : ∀ k, |(x ∘ e) k - zC k| ≤ ρ := by
    intro k
    have h1 : ((x ∘ e) k - zC k) ^ 2 ≤ (x - z) ⬝ᵥ (x - z) := by
      have := Finset.single_le_sum (f := fun j => (x - z) j * (x - z) j)
        (fun j _ => mul_self_nonneg _) (Finset.mem_univ (e k))
      have hz : (x - z) (e k) = (x ∘ e) k - zC k := by
        change x (e k) - zC (e.symm (e k)) = _
        rw [Equiv.symm_apply_apply]
        rfl
      rw [sq, ← hz]
      exact this
    exact (sq_le_sq₀ (abs_nonneg _) hρ0).1 (by rw [sq_abs]; exact h1.trans hx)
  have hR1 : (1 : ℝ) ≤ ROf P η γ := by
    rw [ROf_cast]; exact one_le_pow₀ (by norm_num)
  have hin : InSet P.system P.2.1 ((η : ℝ) + γ / 2) ((τOf P η γ : ℝ) / 2) (ROf P η γ) (x ∘ e) := by
    refine mem_of_near hzC hη0 (by positivity) hρ0 hnear ?_ hW ?_ ?_
    · rw [τOf_cast]
      exact ρ_bound₁ hZ (numVars_pow_le hP)
    · intro S hS
      exact ρ_bound₂ hZ (numVars_pow_le hP) (two_pow_le hlenP) (by positivity)
        ((one_div_le_one_div_of_le (two_pow_pos' _) (two_pow_le hlenP)).trans
          (prod_bounds P (hsets S hS)).2.2) (γ_ge_Zof hγ)
    · rw [ROf_cast]
      calc (2 : ℝ) ^ (3 * Zof P η γ ^ 2) + ρ ≤ 2 ^ (3 * Zof P η γ ^ 2) + 2 ^ (3 * Zof P η γ ^ 2) :=
            add_le_add le_rfl (hρ1.trans (one_le_pow₀ (by norm_num)))
        _ = 2 ^ (3 * Zof P η γ ^ 2 + 1) := by rw [pow_succ]; ring
  refine ⟨?_, ?_⟩
  · change InSet P.system P.2.1 ((η + γ / 2 : ℚ) : ℝ) ((τOf P η γ : ℝ) / 2) (ROf P η γ) (x ∘ e)
    push_cast
    exact hin
  · -- The objective barely moves.
    have hzR : ∀ i, |zC i| ≤ (ROf P η γ : ℝ) := fun i =>
      (hzC.box i).trans (by rw [ROf_cast]; exact two_pow_le (by omega))
    have hobj := abs_obj_sub_le (y := ys (x ∘ e)) (y' := ys zC) (ρ := ρ) (B := ROf P η γ) hq
      fun m _ => ⟨abs_ys_sub_le hρ0 hnear m, abs_ys_le hR1 hin.box m, abs_ys_le hR1 hzR m⟩
    have heq : obj (toReal (P.2.2.2.1.toPoly P.1)) (P.2.2.2.2.map fun q => toReal (q.toPoly P.1))
        (ys zC) = P.objective E' := by
      rw [obj_eq_of_agree E' hagree hq, objective_eq]
    have hbound : ρ * (coeffNorm1 (toReal (P.2.2.2.1.toPoly P.1)) + 2 * (ROf P η γ : ℝ) *
        ((P.2.2.2.2.map fun q => toReal (q.toPoly P.1)).map fun q => coeffNorm1 q ^ 2).sum) ≤
        γ / 2 := by
      rw [ROf_cast]
      refine ρ_bound₃ hZ ((coeffNorm1_obj_le List.mem_cons_self).trans
        (two_pow_le ((length_encRaw_obj_le List.mem_cons_self).trans hlenP)))
        ((sum_sq_obj_le P).trans (two_pow_le (by omega))) (γ_ge_Zof hγ)
    rw [fObj]
    have := (abs_le.1 hobj).2
    rw [heq] at this
    linarith

/-- **The ellipsoid method finds a good center**: for every competitor, some center within `K`
steps is declared feasible, with objective at most the competitor's plus `γ / 2`. -/
theorem exists_good (hP : P.Valid) (hη : 0 < η) (hγ : 0 < γ) (hN : 0 < Nof P)
    (E' : PseudoExpectation (Fin P.1) P.2.1) (hE' : E'.ApproxSatisfies P.system (η : ℝ) 0) :
    ∃ k < Kof P η γ, (orcOf P η γ (stOf P η γ k).1).1 = true ∧
      (objOf P (stOf P η γ k).1 : ℝ) ≤ P.objective E' + γ / 2 := by
  classical
  have : Nonempty (Fin (Nof P)) := ⟨⟨0, hN⟩⟩
  have hZ : 4 ≤ Zof P η γ := four_le_Zof
  have hN1 : 1 ≤ Nof P := hN
  set s : ℝ := 2 ^ (8 * Zof P η γ ^ 2) with hs
  set δ : ℝ := 2 / 2 ^ expP (Zof P η γ) (Nof P) with hδ
  have hs1 : (1 : ℝ) ≤ s := one_le_pow₀ (by norm_num)
  have hs0 : (0 : ℝ) < s := by positivity
  have hP0 : matL (Nof P) (stOf P η γ 0).2.1 = s • (1 : Matrix (Fin (Nof P)) (Fin (Nof P)) ℝ) := by
    change matL (Nof P) (shape₀ (Nof P) (2 ^ (8 * Zof P η γ ^ 2))) = _
    rw [matL_shape₀]
    push_cast
    rfl
  have hc0 : vecL (Nof P) (stOf P η γ 0).1 = 0 := vecL_replicate (Nof P)
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ _ := two_pow_le (by unfold expP; omega)
  have hσ : Ellipsoid.stepSize (Fin (Nof P)) = 1 / (4 * (Nof P : ℝ)) := by
    simp [Ellipsoid.stepSize]
  have hσ1 : Ellipsoid.stepSize (Fin (Nof P)) ≤ 1 :=
    Ellipsoid.stepSize_le.trans (by norm_num)
  have hB : ((2 ^ expB (Zof P η γ) (Nof P) : ℚ) : ℝ) = 2 ^ (2 * Kof P η γ + 1) * s := by
    rw [hs, ← pow_add]
    push_cast
    rfl
  -- The steps.
  have hstep : ∀ k < Kof P η γ,
      (matL (Nof P) (stOf P η γ k).2.1)ᵀ = matL (Nof P) (stOf P η γ k).2.1 →
      (∀ u, s / 4 ^ k * (u ⬝ᵥ u) ≤ u ⬝ᵥ matL (Nof P) (stOf P η γ k).2.1 *ᵥ u) →
      (∀ u, u ⬝ᵥ matL (Nof P) (stOf P η γ k).2.1 *ᵥ u ≤ 2 ^ k * s * (u ⬝ᵥ u)) →
      (∀ i, |vecL (Nof P) (stOf P η γ k).1 i - vecL (Nof P) (stOf P η γ 0).1 i| ≤
        k * (Real.sqrt (2 ^ Kof P η γ * s) + δ)) →
      vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2 ≠ 0 ∧
      (matL (Nof P) (stOf P η γ (k + 1)).2.1)ᵀ = matL (Nof P) (stOf P η γ (k + 1)).2.1 ∧
      (∀ i, |vecL (Nof P) (stOf P η γ (k + 1)).1 i - Ellipsoid.stepCenter
        (vecL (Nof P) (stOf P η γ k).1) (vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2)
        (matL (Nof P) (stOf P η γ k).2.1) i| ≤ δ) ∧
      (∀ i j, |matL (Nof P) (stOf P η γ (k + 1)).2.1 i j - Ellipsoid.stepShape
        (vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2) (matL (Nof P) (stOf P η γ k).2.1) i j| ≤
          δ) ∧
      (¬ (orcOf P η γ (stOf P η γ k).1).1 = true → ∀ x ∈ CSet P η γ,
        vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2 ⬝ᵥ (x - vecL (Nof P) (stOf P η γ k).1) ≤ 0) ∧
      ((orcOf P η γ (stOf P η γ k).1).1 = true → ∀ x ∈ CSet P η γ,
        fObj P x < fObj P (vecL (Nof P) (stOf P η γ k).1) →
        vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2 ⬝ᵥ (x - vecL (Nof P) (stOf P η γ k).1) ≤
          0) := by
    intro k hk hsym hlo hhi hcen
    obtain ⟨hl1, hl2, hl3, -⟩ := lengths_stOf η γ k (P := P)
    have hla := length_orcOf (P := P) (η := η) (γ := γ) hl1
    obtain ⟨ha0, hcut, hobj⟩ := orc_spec (η := η) (γ := γ) hP hN k
    have hnext := stOf_succ η γ k (P := P)
    have hpsd : ∀ u, 0 ≤ u ⬝ᵥ matL (Nof P) (stOf P η γ k).2.1 *ᵥ u := fun u =>
      le_trans (mul_nonneg (by positivity) (Ellipsoid.dotProduct_self_nonneg' u)) (hlo u)
    have hq : 0 < vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2 ⬝ᵥ
        matL (Nof P) (stOf P η γ k).2.1 *ᵥ vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2 := by
      have h1 : 0 < vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2 ⬝ᵥ
          vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2 :=
        lt_of_le_of_ne (Ellipsoid.dotProduct_self_nonneg' _)
          (Ne.symm (mt dotProduct_self_eq_zero.1 ha0))
      exact lt_of_lt_of_le (mul_pos (by positivity) h1) (hlo _)
    have hhi' : ∀ u, u ⬝ᵥ matL (Nof P) (stOf P η γ k).2.1 *ᵥ u ≤ (2 ^ k * s) * (u ⬝ᵥ u) := hhi
    obtain ⟨hcb, hsb⟩ := clamp_bound hk hs1 hδ0 hδ1 hσ1
    have hBc : ∀ i, |Ellipsoid.stepCenter (vecL (Nof P) (stOf P η γ k).1)
        (vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2) (matL (Nof P) (stOf P η γ k).2.1) i| +
        2 / 2 ^ expP (Zof P η γ) (Nof P) ≤ ((2 ^ expB (Zof P η γ) (Nof P) : ℚ) : ℝ) := by
      intro i
      have h1 := Ellipsoid.abs_stepCenter_sub_le hsym hpsd hhi' hq i
        (c := vecL (Nof P) (stOf P η γ k).1)
      have h2 := hcen i
      rw [hc0, Pi.zero_apply, sub_zero] at h2
      rw [hB]
      have h3 : |Ellipsoid.stepCenter (vecL (Nof P) (stOf P η γ k).1)
          (vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2) (matL (Nof P) (stOf P η γ k).2.1) i| ≤
          |Ellipsoid.stepCenter (vecL (Nof P) (stOf P η γ k).1)
            (vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2) (matL (Nof P) (stOf P η γ k).2.1) i -
              vecL (Nof P) (stOf P η γ k).1 i| + |vecL (Nof P) (stOf P η γ k).1 i| := by
        have := abs_sub_abs_le_abs_sub (Ellipsoid.stepCenter (vecL (Nof P) (stOf P η γ k).1)
          (vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2) (matL (Nof P) (stOf P η γ k).2.1) i)
          (vecL (Nof P) (stOf P η γ k).1 i)
        linarith
      have h4 : 2 / 2 ^ expP (Zof P η γ) (Nof P) = δ := rfl
      rw [h4]
      linarith
    have hBP : ∀ i j, |Ellipsoid.stepShape (vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2)
        (matL (Nof P) (stOf P η γ k).2.1) i j| + 2 / 2 ^ expP (Zof P η γ) (Nof P) ≤
        ((2 ^ expB (Zof P η γ) (Nof P) : ℚ) : ℝ) := by
      intro i j
      rw [hB]
      exact (add_le_add (Ellipsoid.abs_stepShape_le hsym hpsd hhi' hq i j) le_rfl).trans hsb
    obtain ⟨hcl, hsh⟩ := stepL_spec hl1 hla hl2 hl3 hq hBc hBP
    refine ⟨ha0, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hnext]
      exact stepL_symm (c := (stOf P η γ k).1) hl2 hl3 hsym
    · intro i
      rw [hnext]
      exact hcl i
    · intro i j
      rw [hnext]
      exact hsh i j
    · intro hf x hx
      exact hcut (by simpa using hf) x hx
    · intro ht x _ hlt
      exact (hobj ht).2 x (Set.mem_univ _) hlt
  -- The starting ellipsoid contains the set.
  have h0s : (matL (Nof P) (stOf P η γ 0).2.1)ᵀ = matL (Nof P) (stOf P η γ 0).2.1 := by
    rw [hP0, Matrix.transpose_smul, Matrix.transpose_one]
  have hquad0 : ∀ u, u ⬝ᵥ matL (Nof P) (stOf P η γ 0).2.1 *ᵥ u = s * (u ⬝ᵥ u) := by
    intro u
    rw [hP0, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  have h0C : ∀ x ∈ CSet P η γ, Ellipsoid.Mem (vecL (Nof P) (stOf P η γ 0).1)
      (matL (Nof P) (stOf P η γ 0).2.1) x := by
    intro x hx
    rw [hc0, hP0]
    apply Ellipsoid.mem_zero_smul_one
    have hbox : ∀ j, |x j| ≤ 2 ^ (3 * Zof P η γ ^ 2 + 1) := by
      intro j
      have := hx.box ((equiv (degsSpec P)).symm j)
      rw [ROf_cast] at this
      have hj : (x ∘ equiv (degsSpec P)) ((equiv (degsSpec P)).symm j) = x j := by
        exact congrArg x ((equiv (degsSpec P)).apply_symm_apply j)
      rw [hj] at this
      exact this
    calc x ⬝ᵥ x = ∑ j, x j * x j := rfl
      _ ≤ ∑ _j : Fin (Nof P), (2 : ℝ) ^ (3 * Zof P η γ ^ 2 + 1) * 2 ^ (3 * Zof P η γ ^ 2 + 1) :=
          Finset.sum_le_sum fun j _ => by
            rw [← abs_mul_abs_self]
            exact mul_le_mul (hbox j) (hbox j) (abs_nonneg _) (by positivity)
      _ = (Nof P : ℝ) * (2 ^ (3 * Zof P η γ ^ 2 + 1)) ^ 2 := by simp [sq]
      _ ≤ s := ball_bound hZ (Nof_le hP)
  -- The determinant drops below the volume of the ball.
  have hK : (1 - 3 * Ellipsoid.stepSize (Fin (Nof P)) / 4) ^ Kof P η γ *
      (matL (Nof P) (stOf P η γ 0).2.1).det <
      ((1 / 2 ^ (32 * Zof P η γ ^ 4)) ^ 2) ^ Fintype.card (Fin (Nof P)) := by
    have hKeq : Kof P η γ = 6 * Fintype.card (Fin (Nof P)) *
        (Nof P * (64 * Zof P η γ ^ 4 + 8 * Zof P η γ ^ 2 + 1)) := by
      simp only [Kof, expK, Fintype.card_fin]
      ring
    have hbase : 0 ≤ 1 - 3 * Ellipsoid.stepSize (Fin (Nof P)) / 4 := by
      have := Ellipsoid.stepSize_le (ι := Fin (Nof P))
      linarith
    rw [hP0, Matrix.det_smul, Matrix.det_one, mul_one, hKeq, pow_mul]
    calc ((1 - 3 * Ellipsoid.stepSize (Fin (Nof P)) / 4) ^ (6 * Fintype.card (Fin (Nof P)))) ^
          (Nof P * (64 * Zof P η γ ^ 4 + 8 * Zof P η γ ^ 2 + 1)) * s ^ Fintype.card (Fin (Nof P))
        ≤ (1 / 2) ^ (Nof P * (64 * Zof P η γ ^ 4 + 8 * Zof P η γ ^ 2 + 1)) *
            s ^ Fintype.card (Fin (Nof P)) := by
          gcongr
          exact Ellipsoid.pow_six_mul_card_le
      _ < _ := by
          rw [Fintype.card_fin]
          exact det_bound hN1
  have hδ₁ : (Fintype.card (Fin (Nof P)) : ℝ) * δ ≤
      Ellipsoid.stepSize (Fin (Nof P)) ^ 2 * (s / 4 ^ Kof P η γ) / 8 := by
    rw [Fintype.card_fin, hσ]
    exact (δ_bounds hN1 hs1).1
  have hδ₂ : (Fintype.card (Fin (Nof P)) : ℝ) * δ ^ 2 ≤
      Ellipsoid.stepSize (Fin (Nof P)) ^ 4 * (s / 4 ^ Kof P η γ) / 128 := by
    rw [Fintype.card_fin, hσ]
    exact (δ_bounds hN1 hs1).2
  obtain ⟨z, hball⟩ := ball_ok hP hη hγ E' hE'
  obtain ⟨k, hk, hfeas, hle⟩ := Ellipsoid.exists_feasible_le (Kof P η γ)
    (fun k => vecL (Nof P) (stOf P η γ k).1)
    (fun k => vecL (Nof P) (orcOf P η γ (stOf P η γ k).1).2)
    (fun k => matL (Nof P) (stOf P η γ k).2.1) (CSet P η γ)
    (fun k => (orcOf P η γ (stOf P η γ k).1).1 = true) (fObj P) (lam := s) (Λ := s) (δ := δ)
    (r := 1 / 2 ^ (32 * Zof P η γ ^ 4)) (v := P.objective E' + γ / 2) (z := z)
    hs0 h0s (fun u => (hquad0 u).ge) (fun u => (hquad0 u).le) h0C hstep hδ₁ hδ₂ (by positivity)
    hball hK
  exact ⟨k, hk, hfeas, by rw [← fObj_vecL]; exact hle⟩

/-- **A competitor's lift is in the relaxed set**, with the competitor's objective. -/
theorem lift_ok (hP : P.Valid) (hη : 0 < η) (hγ : 0 < γ)
    (E' : PseudoExpectation (Fin P.1) P.2.1) (hE' : E'.ApproxSatisfies P.system (η : ℝ) 0) :
    ∃ zC : Coord P.system P.2.1 → ℝ,
      InSet P.system P.2.1 ((η + γ / 2 : ℚ) : ℝ) (τOf P η γ) (ROf P η γ) zC ∧
      obj (toReal (P.2.2.2.1.toPoly P.1)) (P.2.2.2.2.map fun q => toReal (q.toPoly P.1)) (ys zC) =
        P.objective E' := by
  classical
  have hZ : 4 ≤ Zof P η γ := four_le_Zof
  have hη0 : (0 : ℝ) ≤ η := by exact_mod_cast hη.le
  have hγ0 : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hlenP := lenP_le_Zof (P := P) (η := η) (γ := γ)
  have hq : ∀ q ∈ toReal (P.2.2.2.1.toPoly P.1) :: P.2.2.2.2.map fun q => toReal (q.toPoly P.1),
      q.totalDegree ≤ P.2.1 := by
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact (totalDegree_toReal_le _).trans (hP.2.2.1 _ List.mem_cons_self)
    · obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      exact (totalDegree_toReal_le _).trans (hP.2.2.1 _ (List.mem_cons_of_mem _ hq'))
  have hsets : ∀ S ∈ sets P.system P.2.1, ∀ i ∈ S, (P.system.get i).totalDegree ≠ 0 :=
    fun S hS => (Finset.mem_filter.1 hS).2.2.1
  have hW : ∀ S ∈ sets P.system P.2.1, coeffNorm1 (toReal (P.system.prod S)) ≤
      2 ^ (encProblem P).length := fun S hS => (prod_bounds P (hsets S hS)).1
  have hF : ∀ S ∈ sets P.system P.2.1, ∏ i ∈ S, coeffNorm (toReal (P.system.get i)) ≤
      2 ^ (encProblem P).length := fun S hS => (prod_bounds P (hsets S hS)).2.1
  have hR₀ := R₀_bound hZ (Ry := 2 ^ (Zof P η γ ^ 2)) le_rfl (by positivity)
    ((two_pow_le hlenP)) ((two_pow_le hlenP)) (by positivity) (η_le_Zof (P := P) (γ := γ))
  obtain ⟨zC, hzC, hagree⟩ := exists_lift E' hη0 hE'
    (fun m hm => moment_bound (γ := γ) hP hη0 E' hE' m hm) hW hF hR₀.1 hR₀.2
  refine ⟨zC, ?_, by rw [obj_eq_of_agree E' hagree hq, objective_eq]⟩
  have hin : InSet P.system P.2.1 ((η : ℝ) + γ / 2) (τOf P η γ) (ROf P η γ) zC := by
    refine mem_of_near hzC hη0 (by positivity) le_rfl (fun i => by simp) ?_ hW ?_ ?_
    · rw [zero_mul, τOf_cast]
      positivity
    · intro S _
      simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      positivity
    · rw [ROf_cast, add_zero]
      exact two_pow_le (by omega)
  push_cast
  exact hin

theorem isEmpty_coord (hN : Nof P = 0) : IsEmpty (Coord P.system P.2.1) :=
  ⟨fun k => by
    have := (equiv (degsSpec P) k).2
    have h0 : (coordsL P.1 P.2.1 (degs P)).length = 0 := hN
    exact absurd (lt_of_lt_of_eq this h0) (Nat.not_lt_zero _)⟩

/-- **The best center**: in the relaxed set, with objective at most every competitor's plus
`γ / 2`. -/
theorem best_good (hP : P.Valid) (hη : 0 < η) (hγ : 0 < γ) :
    InSet P.system P.2.1 ((η + γ / 2 : ℚ) : ℝ) (τOf P η γ) (ROf P η γ)
        (pt (degsSpec P) (if (stOf P η γ (Kof P η γ)).2.2.1 then (stOf P η γ (Kof P η γ)).2.2.2
          else List.replicate (Nof P) 0)) ∧
      ∀ E' : PseudoExpectation (Fin P.1) P.2.1, E'.ApproxSatisfies P.system (η : ℝ) 0 →
        obj (toReal (P.2.2.2.1.toPoly P.1)) (P.2.2.2.2.map fun q => toReal (q.toPoly P.1))
          (ys (pt (degsSpec P) (if (stOf P η γ (Kof P η γ)).2.2.1 then
            (stOf P η γ (Kof P η γ)).2.2.2 else List.replicate (Nof P) 0))) ≤
          P.objective E' + γ / 2 := by
  classical
  have hη0 : (0 : ℝ) ≤ η := by exact_mod_cast hη.le
  have hγ0 : (0 : ℝ) < γ := by exact_mod_cast hγ
  obtain ⟨y, hy⟩ := hP.2.2.2.2
  have hE₀ := ofPoint_approxSatisfies (ℓ := P.2.1) hy hη0
  rcases Nat.eq_zero_or_pos (Nof P) with hN | hN
  · -- No coordinates: every point is the lift of every competitor.
    have := isEmpty_coord hN
    have hall : ∀ x x' : Coord P.system P.2.1 → ℝ, x = x' := fun x x' =>
      funext fun k => isEmptyElim k
    generalize pt (degsSpec P) (if (stOf P η γ (Kof P η γ)).2.2.1 then
      (stOf P η γ (Kof P η γ)).2.2.2 else List.replicate (Nof P) 0) = X
    obtain ⟨zC, hzC, -⟩ := lift_ok hP hη hγ _ hE₀
    refine ⟨by rw [hall X zC]; exact hzC, fun E' hE' => ?_⟩
    obtain ⟨zC', -, hobj⟩ := lift_ok hP hη hγ E' hE'
    rw [hall X zC', hobj]
    linarith
  · have hbs : ((stOf P η γ (Kof P η γ)).2.2.1 = true ↔
          ∃ k < Kof P η γ, (orcOf P η γ (stOf P η γ k).1).1 = true) ∧
        ((stOf P η γ (Kof P η γ)).2.2.1 = true → ∃ j < Kof P η γ,
          (orcOf P η γ (stOf P η γ j).1).1 = true ∧
          (stOf P η γ (Kof P η γ)).2.2.2 = (stOf P η γ j).1 ∧
          ∀ k < Kof P η γ, (orcOf P η γ (stOf P η γ k).1).1 = true →
            objOf P (stOf P η γ j).1 ≤ objOf P (stOf P η γ k).1) :=
      best_spec _ _ _ _ _ _ _ _
    obtain ⟨k₀, hk₀, hfeas₀, -⟩ := exists_good hP hη hγ hN _ hE₀
    have hfound : (stOf P η γ (Kof P η γ)).2.2.1 = true := hbs.1.2 ⟨k₀, hk₀, hfeas₀⟩
    obtain ⟨j, hj, hfeasj, hbest, hmin⟩ := hbs.2 hfound
    have hbest' : (if (stOf P η γ (Kof P η γ)).2.2.1 then (stOf P η γ (Kof P η γ)).2.2.2
        else List.replicate (Nof P) 0) = (stOf P η γ j).1 := by
      rw [ite_eq_left hfound]
      exact hbest
    rw [hbest']
    refine ⟨((orc_spec (η := η) (γ := γ) hP hN j).2.2 hfeasj).1, fun E' hE' => ?_⟩
    obtain ⟨k, hk, hfeas, hle⟩ := exists_good hP hη hγ hN E' hE'
    have h1 : (objOf P (stOf P η γ j).1 : ℝ) ≤ objOf P (stOf P η γ k).1 := by
      exact_mod_cast hmin k hk hfeas
    rw [obj_pt]
    exact h1.trans hle

end Main

/-! ### The output -/

/-- **The algorithm is correct.** -/
theorem core_correct (P : Problem) (hP : P.Valid) (η γ : ℚ) (hη : 0 < η) (hγ : 0 < γ) :
    Correct P η γ (core ((P, η, γ), budget (P, η, γ))) := by
  classical
  obtain ⟨hin, hopt⟩ := best_good hP hη hγ
  rw [core_eq η γ hP]
  generalize hb : (if (stOf P η γ (Kof P η γ)).2.2.1 then (stOf P η γ (Kof P η γ)).2.2.2
    else List.replicate (Nof P) 0) = best at hin hopt
  have hZ : 4 ≤ Zof P η γ := four_le_Zof
  have hη0 : (0 : ℝ) ≤ η := by exact_mod_cast hη.le
  have hγ0 : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hlenP := lenP_le_Zof (P := P) (η := η) (γ := γ)
  have hev : Even P.2.1 := hP.1
  have he := enough hP (η, γ)
  have he' : Enough (budget (P, η, γ)) P.1 0 P.2.1 :=
    ⟨he.deg, he.vars, by simpa using (Nat.one_le_pow _ _ (Nat.succ_pos _)).trans he.vars⟩
  have hL := budget_le_Zof (P := P) (η := η) (γ := γ)
  set X := pt (degsSpec P) best
  set t : ℚ := 1 / 2 ^ (8 * Zof P η γ ^ 2)
  set μ : (Fin P.1 →₀ ℕ) → ℝ := fun m => (gridMoment (P.2.1 / 2) m : ℝ)
  set D : ℝ := 2 ^ (Zof P η γ ^ 2)
  have ht : (0 : ℝ) < t := by simp only [t]; positivity
  have hR1 : (1 : ℝ) ≤ ROf P η γ := by rw [ROf_cast]; exact one_le_pow₀ (by norm_num)
  have hq : ∀ q ∈ toReal (P.2.2.2.1.toPoly P.1) :: P.2.2.2.2.map fun q => toReal (q.toPoly P.1),
      q.totalDegree ≤ P.2.1 := by
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact (totalDegree_toReal_le _).trans (hP.2.2.1 _ List.mem_cons_self)
    · obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      exact (totalDegree_toReal_le _).trans (hP.2.2.1 _ (List.mem_cons_of_mem _ hq'))
  have hsets : ∀ S ∈ sets P.system P.2.1, ∀ i ∈ S, (P.system.get i).totalDegree ≠ 0 :=
    fun S hS => (Finset.mem_filter.1 hS).2.2.1
  -- The grid moments.
  have hμ0 : μ 0 = 1 := by simp [μ]
  have hμ : MinEigGE (riesz μ) P.2.1 (gridEig P.1 (P.2.1 / 2)) := by
    have := minEigGE_gridMoment (σ := Fin P.1) (P.2.1 / 2)
    rw [Nat.two_mul_div_two_of_even hev, Fintype.card_fin] at this
    exact this
  have hμb : ∀ m : Fin P.1 →₀ ℕ, m.degree ≤ P.2.1 → |μ m| ≤ D := by
    intro m hm
    refine (abs_gridMoment_le _ m).trans ?_
    have hd : ((P.2.1 / 2 : ℕ) : ℝ) ≤ 2 ^ Zof P η γ := by
      exact_mod_cast (Nat.div_le_self _ _).trans (he.deg.trans (by omega) |>.trans
        (Nat.lt_two_pow_self).le)
    calc ((P.2.1 / 2 : ℕ) : ℝ) ^ m.degree ≤ (2 ^ Zof P η γ) ^ m.degree :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hd _
      _ ≤ (2 ^ Zof P η γ) ^ Zof P η γ :=
          pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (hm.trans (he.deg.trans (by omega)))
      _ = D := by rw [← pow_mul]; change _ = (2 : ℝ) ^ (Zof P η γ ^ 2); rw [sq]
  have hτ : (τOf P η γ : ℝ) ≤ t * gridEig P.1 (P.2.1 / 2) := by
    rw [τOf_cast]
    simp only [t]
    push_cast
    exact τ_bound hZ ((numVars_le hP).trans hlenP) ((Nat.div_le_self _ _).trans
      (he.deg.trans (by omega)))
  have hW : ∀ S ∈ sets P.system P.2.1, coeffNorm1 (toReal (P.system.prod S)) ≤
      2 ^ (encProblem P).length := fun S hS => (prod_bounds P (hsets S hS)).1
  have hdist : ∀ S ∈ sets P.system P.2.1, (Fintype.card (Fin P.1) + 1 : ℝ) ^ P.2.1 *
      ((t : ℝ) * ((2 ^ (encProblem P).length + 1) * D)) ^ 2 ≤
      ((γ - γ / 2) * ∏ i ∈ S, coeffNorm (toReal (P.system.get i))) ^ 2 := by
    intro S hS
    have := t_bound₁ hZ (numVars_pow_le hP) (two_pow_le hlenP) (by positivity) le_rfl
      (by positivity) ((one_div_le_one_div_of_le (two_pow_pos' _) (two_pow_le hlenP)).trans
        (prod_bounds P (hsets S hS)).2.2) (γ_ge_Zof hγ)
    simpa [t] using this
  have hA : ∀ i, (P.system.get i).totalDegree = 0 →
      0 ≤ algebraMap ℚ ℝ ((P.system.get i).coeff 0) := by
    intro i hi
    obtain ⟨y, hy⟩ := hP.2.2.2.2
    have h1 := hy _ (List.get_mem P.system i)
    rw [totalDegree_eq_zero_iff_eq_C.1 hi, toReal, map_C, eval_C] at h1
    exact h1
  have hin' : InSet P.system P.2.1 ((η : ℝ) + γ / 2) (τOf P η γ) (ROf P η γ) X := by
    have := hin
    push_cast at this
    exact this
  obtain ⟨h0, hpsd, happ⟩ := output hin' hμ0 hμ hμb ht hτ hη0 (by positivity)
    (by linarith) hW hdist hA
  refine ⟨PseudoExpectation.ofMoments _ h0 hpsd, ?_, happ, fun E' hE' => ?_⟩
  · -- The moments.
    intro α hα
    rw [PseudoExpectation.ofMoments_apply_monomial, mix_apply,
      coeff_outputL he' (csOf P) best t α hα, ys_pt]
    simp only [μ, t]
    push_cast
    rfl
  · -- Approximate optimality.
    have hobj : P.objective (PseudoExpectation.ofMoments _ h0 hpsd) =
        obj (toReal (P.2.2.2.1.toPoly P.1)) (P.2.2.2.2.map fun q => toReal (q.toPoly P.1))
          (mix t μ (ys X)) := by
      rw [objective_eq, obj, List.map_map, List.map_map]
      rfl
    have hmix := abs_obj_mix_sub_le hR1 hin'.box hμb ht.le hq
    have hbound : (t : ℝ) * ((ROf P η γ : ℝ) + D) * (coeffNorm1 (toReal (P.2.2.2.1.toPoly P.1)) +
        2 * ((ROf P η γ : ℝ) + D) *
          ((P.2.2.2.2.map fun q => toReal (q.toPoly P.1)).map fun q => coeffNorm1 q ^ 2).sum) ≤
        γ / 2 := by
      rw [ROf_cast]
      have := t_bound₂ hZ ((coeffNorm1_obj_le List.mem_cons_self).trans
        (two_pow_le ((length_encRaw_obj_le List.mem_cons_self).trans hlenP)))
        ((sum_sq_obj_le P).trans (two_pow_le (by omega))) le_rfl (by positivity) (γ_ge_Zof hγ)
      simpa [t] using this
    have h2 := hopt E' hE'
    rw [hobj]
    have := (abs_le.1 hmix).2
    linarith

end SoS.Correct

/-! ### The solver -/

namespace SoS.Solver

/-- **The sum-of-squares algorithm** [BKS23, Fact 3.6]: one Turing machine solves every valid
problem to any accuracies `η, γ > 0` within the time bound `timeBound C`. (The space bound, the
time plus the length of the input, is no restriction.) The machine runs `SoS.Core.core` with the
budget `SoS.Solver.budget` (`SoS.PolyTime.core_polytime`,
`SoS.Solver.exists_computableInTimeAndSpace_of_budget`), and its answer is correct
(`SoS.Correct.core_correct`). -/
theorem exists_solver : ∃ (C : ℕ) (solve : Input → Output),
    Turing.MultiTapeTM.ComputableInTimeAndSpace solve encInput encOutput
      (timeBound C) (fun x ↦ timeBound C x + (encInput x).length) ∧
    ∀ P : Problem, P.Valid → ∀ η γ : ℚ, 0 < η → 0 < γ → Correct P η γ (solve (P, η, γ)) := by
  obtain ⟨C, hC⟩ := exists_computableInTimeAndSpace_of_budget SoS.PolyTime.core_polytime
  exact ⟨C, fun x => SoS.Core.core (x, budget x), hC,
    fun P hP η γ hη hγ => SoS.Correct.core_correct P hP η γ hη hγ⟩

end SoS.Solver
