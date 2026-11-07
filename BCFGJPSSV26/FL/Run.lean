module

public import BCFGJPSSV26.FL.Select
public import BCFGJPSSV26.Greedy.Alg.Core

/-!
# Theorem 1.4: the greedy run

The guarantee of the greedy run (`BCFGJPSSV26.FL.runFL_spec`): if `n ≥ 2`, `m ≥ 2`, `f > 0`
and a nonempty set `O` has a positive cost, the run is a list of distinct facilities `S` with
`cost S + λ f |S| ≤ λ (cost O + f |O|)`.

* **The scaled space** (`BCFGJPSSV26.FL.scSpace`): `d / t + 1` off the diagonal, a pseudometric
  with client–facility distances at least `1`. As clients and facilities are distinct points,
  every set of facilities costs `cost / t + n` there (`BCFGJPSSV26.FL.coreCost_ctxFL`,
  `BCFGJPSSV26.FL.costF_scSpace`).
* **The context** satisfies the hypotheses of `Greedy/Alg/Bridge.lean`
  (`BCFGJPSSV26.FL.hyp_ctxFL`), so CompleteSolution gives a `0`-valid solution
  (`BCFGJPSSV26.Greedy.Ctx.complete_sol`) at the scaled opening cost `f̂ = λ (1 - δ) f / t`.
* **The robust LMP guarantee** (`BCFGJPSSV26.Greedy.robust_lmp`) applies with slack `η = 0`
  (validity and solutions do not depend on the slack parameter, `BCFGJPSSV26.FL.sol_eta`):
  `(1 - δ) connCost + s f̂ ≤ (ρ + 6δ) cost(O) + |O| f̂` for the `s` regular atoms of the solution.
  Scaled back by `t / (1 - δ)`, with `ρ' = (ρ + 6δ) / (1 - δ)`,
  `cost S + λ f |S| ≤ ρ' cost O + (ρ' - 1) n t + λ f |O|`. Since `cost O ≥ d_min` and
  `n t ≤ d_min / 10⁵`, this is at most `λ (cost O + f |O|)` for `δ = 10⁻⁶`
  (`BCFGJPSSV26.FL.fl_arith`).
-/

@[expose] public section

namespace BCFGJPSSV26.FL

open Finset Greedy

variable {I : Instance}

/-! ### The scaled space -/

/-- **The scaled pseudometric**: `d / t + 1` off the diagonal. -/
def scSpace (I : Instance) (hI : I.Valid) (t : ℚ) (ht : 0 < t) : Space I.n I.m where
  D a b := if a = b then 0 else I.d a b / t + 1
  nonneg a b := by
    split_ifs
    · exact le_rfl
    · have := div_nonneg (hI.nonneg a b) ht.le
      linarith
  self a := by simp
  comm a b := by
    by_cases h : a = b
    · subst h; rfl
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), hI.comm]
  triangle a b c := by
    have hnn : ∀ a b, 0 ≤ (if a = b then 0 else I.d a b / t + 1) := fun a b ↦ by
      split_ifs
      · exact le_rfl
      · have := div_nonneg (hI.nonneg a b) ht.le
        linarith
    by_cases hac : a = c
    · rw [ite_eq_left hac]
      exact add_nonneg (hnn a b) (hnn b c)
    by_cases hab : a = b
    · subst hab
      simp
    by_cases hbc : b = c
    · subst hbc
      simp
    rw [ite_eq_right hac, ite_eq_right hab, ite_eq_right hbc]
    have h : I.d a c / t ≤ I.d a b / t + I.d b c / t := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (hI.triangle a b c) ht.le
    linarith

/-- The scaled client–facility distances. -/
theorem scSpace_d {hI : I.Valid} {t : ℚ} {ht : 0 < t} (j : Fin I.n) (i : Fin I.m) :
    (scSpace I hI t ht).d j i = I.d (.inl j) (.inr i) / t + 1 := by
  simp [Space.d, scSpace]

/-- The entries of the scaled table, `0` outside it. -/
theorem stabFL_getD (x : Raw) (f : ℚ) (j i : ℕ) :
    ((stabFL x f).getD j []).getD i 0 =
      if j < x.n ∧ i < x.m then x.fdist j i / tFL x f + 1 else 0 := by
  by_cases hj : j < x.n
  · by_cases hi : i < x.m
    · rw [ite_eq_left ⟨hj, hi⟩]
      simp [stabFL, List.getD_eq_getElem?_getD, hj, hi]
    · rw [ite_eq_right fun h ↦ hi h.2]
      simp [stabFL, List.getD_eq_getElem?_getD, hj, hi]
  · rw [ite_eq_right fun h ↦ hj h.1]
    simp [stabFL, List.getD_eq_getElem?_getD, hj]

theorem stabFL_entry (f : ℚ) (j : Fin I.n) (i : Fin I.m) :
    ((stabFL (toRaw I) f).getD j []).getD i 0 = I.d (.inl j) (.inr i) / tFL (toRaw I) f + 1 := by
  rw [stabFL_getD, ite_eq_left ⟨j.2, i.2⟩, ← Raw.fdist_toRaw (.inl j) i]
  rfl

/-! ### The least positive distance -/

theorem mem_guesses_toRaw {j : Fin I.n} {i : Fin I.m} (h : 0 < I.d (.inl j) (.inr i)) :
    I.d (.inl j) (.inr i) ∈ guesses (toRaw I) := by
  unfold guesses
  rw [List.mem_filter, decide_eq_true_iff]
  refine ⟨List.mem_flatMap.2 ⟨j, by simp, List.mem_map.2 ⟨i, by simp, ?_⟩⟩, h⟩
  exact Raw.fdist_toRaw (.inl j) i

theorem pos_of_mem_guesses {x : Raw} {q : ℚ} (h : q ∈ guesses x) : 0 < q := by
  unfold guesses at h
  exact of_decide_eq_true (List.mem_filter.1 h).2

/-- **The least positive distance** is positive and at most every positive cost. -/
theorem dminFL_spec (hI : I.Valid) {O : Finset (Fin I.m)} (hO : O.Nonempty)
    (h : 0 < ∑ j, O.inf' hO fun i ↦ I.d (.inl j) (.inr i)) :
    0 < dminFL (toRaw I) ∧ dminFL (toRaw I) ≤ ∑ j, O.inf' hO fun i ↦ I.d (.inl j) (.inr i) := by
  obtain ⟨j, -, hj⟩ := exists_lt_of_sum_lt (s := univ) (f := fun _ ↦ (0 : ℚ))
    (by simpa using h)
  obtain ⟨i, -, he⟩ := exists_mem_eq_inf' hO fun i ↦ I.d (.inl j) (.inr i)
  have hpos : 0 < I.d (.inl j) (.inr i) := he ▸ hj
  have hmem := mem_guesses_toRaw hpos
  obtain ⟨hm, hle⟩ := Combine.minQ_spec (List.ne_nil_of_mem hmem)
  refine ⟨pos_of_mem_guesses hm, (hle _ hmem).trans ?_⟩
  rw [← he]
  exact single_le_sum (f := fun j ↦ O.inf' hO fun i ↦ I.d (.inl j) (.inr i))
    (fun j _ ↦ le_inf' _ _ fun i _ ↦ hI.nonneg _ _) (mem_univ j)

/-- The cost of a nonempty set, computed exactly. -/
theorem cast_costO {O : Finset (Fin I.m)} (hO : O.Nonempty) :
    ((∑ j, O.inf' hO fun i ↦ I.d (.inl j) (.inr i) : ℚ) : ℝ) = I.cost O := by
  rw [← Instance.costF_eq_cost hO, Instance.costF, Rat.cast_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  obtain ⟨i₀, hi₀, he⟩ := exists_mem_eq_inf' hO fun i ↦ I.d (.inl j) (.inr i)
  refine le_antisymm (Instance.le_dSet hO fun i hi ↦ ?_) ?_
  · unfold Instance.dd
    exact_mod_cast inf'_le (fun i ↦ I.d (.inl j) (.inr i)) hi
  · refine (Instance.dSet_le hi₀ _).trans (le_of_eq ?_)
    unfold Instance.dd
    rw [he]

/-! ### Costs in the scaled space -/

/-- The least of an affine image `g / t + 1` is the affine image of the least. -/
theorem minQ_map_affine {β : Type} {l : List β} (hl : l ≠ []) (g : β → ℚ) {t : ℚ}
    (ht : 0 < t) : Combine.minQ (l.map fun b ↦ g b / t + 1) = Combine.minQ (l.map g) / t + 1 := by
  obtain ⟨h1, h2⟩ := Combine.minQ_spec (l := l.map g) (by simpa using hl)
  obtain ⟨h3, h4⟩ := Combine.minQ_spec (l := l.map fun b ↦ g b / t + 1) (by simpa using hl)
  obtain ⟨b1, hb1, e1⟩ := List.mem_map.1 h1
  obtain ⟨b3, hb3, e3⟩ := List.mem_map.1 h3
  refine le_antisymm ?_ ?_
  · have := h4 (g b1 / t + 1) (List.mem_map.2 ⟨b1, hb1, rfl⟩)
    rwa [e1] at this
  · rw [← e3]
    have := div_le_div_of_nonneg_right (h2 _ (List.mem_map.2 ⟨b3, hb3, rfl⟩)) ht.le
    linarith

/-- **The scaled cost of a list of facilities** is `cost / t + n`. -/
theorem coreCost_ctxFL {f : ℚ} {S : List ℕ} (hS : S ≠ []) (hm : ∀ i ∈ S, i < I.m)
    (ht : 0 < tFL (toRaw I) f) :
    coreCost ((ctxFL (toRaw I) f).ip.n, (ctxFL (toRaw I) f).ip.m, (ctxFL (toRaw I) f).ip.k,
      (ctxFL (toRaw I) f).tab) S = (toRaw I).cost S / tFL (toRaw I) f + I.n := by
  have hlen : min (distTable I).length I.n = I.n := by simp [distTable]
  unfold coreCost Raw.cost Combine.costQ
  change ((List.range I.n).map fun j ↦ Combine.minQ (S.map fun i ↦
    ((stabFL (toRaw I) f).getD j []).getD i 0)).sum =
      ((List.range (min (distTable I).length I.n)).map fun j ↦ Combine.minQ (S.map fun i ↦
        ((distTable I).getD j []).getD (I.n + i) 0)).sum / tFL (toRaw I) f + I.n
  rw [hlen, Ctx.list_sum_map_range, Ctx.list_sum_map_range, sum_div]
  have hn : (I.n : ℚ) = ∑ _j ∈ range I.n, (1 : ℚ) := by simp
  rw [hn, ← sum_add_distrib]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' : j < I.n := mem_range.1 hj
  have e : (S.map fun i ↦ ((stabFL (toRaw I) f).getD j []).getD i 0) =
      S.map fun i ↦ (toRaw I).fdist j i / tFL (toRaw I) f + 1 :=
    List.map_congr_left fun i hi ↦ by
      rw [stabFL_getD, ite_eq_left ⟨hj', hm i hi⟩]
  rw [e, minQ_map_affine hS _ ht]
  rfl

/-- **The scaled cost of a nonempty set** is `cost / t + n`. -/
theorem costF_scSpace {hI : I.Valid} {t : ℚ} {ht : 0 < t} {O : Finset (Fin I.m)}
    (hO : O.Nonempty) :
    costF (scSpace I hI t ht).d O = (∑ j, O.inf' hO fun i ↦ I.d (.inl j) (.inr i)) / t + I.n := by
  unfold costF
  simp only [dite_eq_left hO]
  rw [sum_div]
  have hn : (I.n : ℚ) = ∑ _j : Fin I.n, (1 : ℚ) := by simp
  rw [hn, ← sum_add_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  obtain ⟨i₀, hi₀, he⟩ := exists_mem_eq_inf' hO fun i ↦ I.d (.inl j) (.inr i)
  refine le_antisymm ?_ (le_inf' _ _ fun i hi ↦ ?_)
  · refine (inf'_le _ hi₀).trans (le_of_eq ?_)
    rw [scSpace_d, he]
  · rw [scSpace_d]
    have := div_le_div_of_nonneg_right (inf'_le (fun i ↦ I.d (.inl j) (.inr i)) hi) ht.le
    linarith

/-! ### The hypotheses on the context -/

theorem fhatFL_nonneg {x : Raw} {f : ℚ} (hf : 0 ≤ f) (ht : 0 < tFL x f) : 0 ≤ fhatFL x f := by
  unfold fhatFL lmpC δ0
  have := ht.le
  positivity

/-- **The hypotheses of `Greedy/Alg/Bridge.lean` hold** for the context of the greedy run on the
scaled space, when `n ≥ 2` and `m ≥ 2` (the bound `M` is computed from the instance, the other
parameters as in `BCFGJPSSV26.Greedy.hyp_ctx`). -/
theorem hyp_ctxFL (hI : I.Valid) (hn : 2 ≤ I.n) (hm : 2 ≤ I.m) {f : ℚ} (hf : 0 ≤ f)
    (ht : 0 < tFL (toRaw I) f) : (ctxFL (toRaw I) f).Hyp (scSpace I hI _ ht) := by
  have hn' : (2 : ℚ) ≤ (toRaw I).n := by exact_mod_cast hn
  have hfh := fhatFL_nonneg hf ht
  have hdmax : ∀ (j : Fin I.n) (i : Fin I.m), I.d (.inl j) (.inr i) ≤ (toRaw I).dMaxQ := by
    intro j i
    have h1 := Instance.dd_lt_dMax hI (.inl j) (.inr i)
    rw [← Raw.dMaxQ_toRaw] at h1
    unfold Instance.dd at h1
    exact_mod_cast h1.le
  have hdM0 : 0 < (toRaw I).dMaxQ := by
    have := Instance.dMax_pos hI
    rw [← Raw.dMaxQ_toRaw] at this
    exact_mod_cast this
  have hM1 : 1 ≤ MFL (toRaw I) f := by
    unfold MFL
    have := div_nonneg hdM0.le ht.le
    linarith
  have hε : (0 : ℚ) < ε0 := by norm_num [ε0, δ0]
  have hδ : (0 : ℚ) < δ0 := by norm_num [δ0]
  have hη : 0 < ηFL (toRaw I).n := by
    unfold ηFL
    have : (0 : ℚ) < (toRaw I).n := by linarith
    positivity
  have hd1 : ∀ (j : Fin I.n) (i : Fin I.m), 1 ≤ (scSpace I hI _ ht).d j i := fun j i ↦ by
    rw [scSpace_d]
    have := div_nonneg (hI.nonneg (.inl j) (.inr i)) ht.le
    linarith
  have hdM : ∀ (j : Fin I.n) (i : Fin I.m), (scSpace I hI _ ht).d j i ≤ MFL (toRaw I) f :=
    fun j i ↦ by
      rw [scSpace_d]
      unfold MFL
      have := div_le_div_of_nonneg_right (hdmax j i) ht.le
      linarith
  have hn'' : (2 : ℚ) ≤ I.n := hn'
  refine
    { dist_eq := fun j i ↦ ?_
      dist_nonneg := fun j i ↦ ?_
      d1 := hd1
      dM := hdM
      two_le_n := hn
      one_le_k := le_rfl
      k_lt_n := hn
      k_lt_m := hm
      good := ?_
      one_le_M := hM1
      η_eq := rfl
      fmin_eq := rfl
      fmax_eq := rfl
      one_le_R := Nat.le_add_left 1 _
      θ_last := ?_
      K_eq := rfl
      fstep := ?_
      ustep := hyp_ctx_step_le hη
      L_ge := le_rfl }
  · exact (stabFL_entry f j i).trans (scSpace_d j i).symm
  · change 0 ≤ ((stabFL (toRaw I) f).getD j []).getD i 0
    rw [stabFL_getD]
    split_ifs with h
    · obtain ⟨hj, hi⟩ := h
      rw [show (toRaw I).fdist j i = I.d (.inl ⟨j, hj⟩) (.inr ⟨i, hi⟩) from
        Raw.fdist_toRaw (.inl ⟨j, hj⟩) ⟨i, hi⟩]
      have := div_nonneg (hI.nonneg (.inl ⟨j, hj⟩) (.inr ⟨i, hi⟩)) ht.le
      linarith
    · exact le_rfl
  · refine ⟨hδ, show δ0 ≤ 1 / 100 by norm_num [δ0], hε, le_rfl, hη.le, ?_, le_rfl⟩
    change ((toRaw I).n : ℚ) * ηFL (toRaw I).n ≤ δ0 * ε0 / 10
    have h1 := eta_bound (n := ((toRaw I).n : ℚ)) (s := 1) (δ := δ0) (by linarith) (by linarith)
    unfold ηFL
    rw [one_mul] at h1
    rw [show δ0 * ε0 / 10 = δ0 ^ 2 / 100 by unfold ε0; ring]
    exact h1
  · change 4 * ((toRaw I).n : ℚ) * MFL (toRaw I) f + γ * MFL (toRaw I) f ≤
      (1 + ε0 ^ 2) ^ (RFL (toRaw I) f - 1)
    have hR : RFL (toRaw I) f - 1 =
        ⌈1 / ε0 ^ 2⌉₊ * Nat.clog 2 ⌈5 * ((toRaw I).n : ℚ) * MFL (toRaw I) f⌉₊ := by
      simp [RFL]
    rw [hR]
    refine le_trans ?_ (hyp_ctx_bernoulli hε _)
    have h1 : 5 * ((toRaw I).n : ℚ) * MFL (toRaw I) f ≤
        ⌈5 * ((toRaw I).n : ℚ) * MFL (toRaw I) f⌉₊ := Nat.le_ceil _
    have h2 : (⌈5 * ((toRaw I).n : ℚ) * MFL (toRaw I) f⌉₊ : ℚ) ≤
        2 ^ Nat.clog 2 ⌈5 * ((toRaw I).n : ℚ) * MFL (toRaw I) f⌉₊ := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) _
    have h3 : γ * MFL (toRaw I) f ≤ (toRaw I).n * MFL (toRaw I) f :=
      mul_le_mul_of_nonneg_right (by norm_num [γ]; linarith) (by linarith)
    linarith
  · change (4 * ((toRaw I).n : ℚ) * MFL (toRaw I) f - δ0) / 2 ^ Nat.clog 2
      ⌈4 * ((toRaw I).n : ℚ) * MFL (toRaw I) f / ηFL (toRaw I).n⌉₊ ≤ ηFL (toRaw I).n
    refine le_trans ?_ (hyp_ctx_step_le (A := 4 * ((toRaw I).n : ℚ) * MFL (toRaw I) f) hη)
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-! ### The robust LMP guarantee with slack `0` -/

/-- Solutions do not depend on the slack parameter `η` of the parameters (only on the slack
argument). -/
theorem sol_eta {n m : ℕ} {P : Par} {d : Fin n → Fin m → ℚ} {f η : ℚ}
    {H : List (List (Atom m))} (h : Sol P d f η H) (η' : ℚ) : Sol { P with η := η' } d f η H :=
  h

/-- **The arithmetic of the guarantee**: from the robust LMP guarantee in the scaled space, with
`cost / t + n` for the costs, `f̂ = λ (1 - δ) f / t` and `n t ≤ d_min / 10⁵ ≤ cost(O) / 10⁵`. -/
theorem fl_arith {t A B cs co s sl o f fh dm n : ℚ} (ht : 0 < t) (hf : 0 ≤ f)
    (hfh : fh = lmpC * (1 - δ0) * f / t) (hA : cs / t + n ≤ A) (hB : B = co / t + n)
    (hsl : sl ≤ s) (hnt : n * t ≤ dm / cS) (hdm0 : 0 < dm) (hdm : dm ≤ co)
    (hlmp : (1 - δ0) * A + s * fh ≤ (ρ + 6 * δ0) * B + o * fh + s * n * 0) :
    cs + lmpC * f * sl ≤ lmpC * (co + f * o) := by
  have hfh0 : 0 ≤ fh := by
    rw [hfh]
    unfold lmpC δ0
    have := ht.le
    positivity
  have h1 : sl * fh ≤ s * fh := mul_le_mul_of_nonneg_right hsl hfh0
  rw [ρ_eq] at hlmp
  have h2 : (1 - δ0) * (cs / t + n) + sl * fh ≤
      (30466 / 15625 + 6 * δ0) * (co / t + n) + o * fh := by
    rw [← hB]
    unfold δ0 at hlmp ⊢
    linarith
  have ht0 := ht.ne'
  have e1 : ((1 - δ0) * (cs / t + n) + sl * fh) * t =
      (1 - δ0) * (cs + n * t) + lmpC * (1 - δ0) * f * sl := by
    rw [hfh]
    field_simp
  have e2 : ((30466 / 15625 + 6 * δ0) * (co / t + n) + o * fh) * t =
      (30466 / 15625 + 6 * δ0) * (co + n * t) + lmpC * (1 - δ0) * f * o := by
    rw [hfh]
    field_simp
  have h3 := mul_le_mul_of_nonneg_right h2 ht.le
  rw [e1, e2] at h3
  have h4 : n * t ≤ co / cS := hnt.trans (div_le_div_of_nonneg_right hdm (by norm_num [cS]))
  unfold lmpC δ0 cS at *
  linarith

/-- **The guarantee of the greedy run**: for `n ≥ 2`, `m ≥ 2`, `f > 0` and a nonempty set `O`
of positive cost, the run is a list of distinct facilities with
`cost S + λ f |S| ≤ λ (cost O + f |O|)`. -/
theorem runFL_spec (hI : I.Valid) (hn : 2 ≤ I.n) (hm : 2 ≤ I.m) {f : ℚ} (hf : 0 < f)
    {O : Finset (Fin I.m)} (hO : O.Nonempty) (hc : 0 < I.cost O) :
    I.IsCenterList (runFL (toRaw I) f) ∧
      (score (toRaw I) f (runFL (toRaw I) f) : ℝ) ≤ (lmpC : ℝ) * (I.cost O + f * O.card) := by
  obtain ⟨co, hco_def⟩ : ∃ co : ℚ, co = ∑ j, O.inf' hO fun i ↦ I.d (.inl j) (.inr i) :=
    ⟨_, rfl⟩
  have hco : (co : ℝ) = I.cost O := by rw [hco_def]; exact cast_costO hO
  have hco_pos : 0 < co := by exact_mod_cast (hco ▸ hc)
  obtain ⟨hdm_pos, hdm_le⟩ := dminFL_spec hI hO (hco_def ▸ hco_pos)
  rw [← hco_def] at hdm_le
  have hn0 : (0 : ℚ) < I.n := by exact_mod_cast (show 0 < I.n by omega)
  have hn1 : (1 : ℚ) ≤ I.n := by exact_mod_cast (show 1 ≤ I.n by omega)
  have ht : 0 < tFL (toRaw I) f := lt_min (div_pos hdm_pos (mul_pos (by norm_num [cS]) hn0)) hf
  have hX := hyp_ctxFL hI hn hm hf.le ht
  -- the opening cost
  have hfh0 := fhatFL_nonneg hf.le ht
  have hfh1 : lmpC * (1 - δ0) ≤ fhatFL (toRaw I) f := by
    unfold fhatFL
    rw [le_div_iff₀ ht]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num [lmpC, δ0])
  have hnη : ((ctxFL (toRaw I) f).ip.n : ℚ) * (ctxFL (toRaw I) f).ip.η <
      fhatFL (toRaw I) f := by
    change ((toRaw I).n : ℚ) * ηFL (toRaw I).n < _
    have h1 := eta_bound (n := ((toRaw I).n : ℚ)) (s := 1) (δ := δ0) hn0 (by
      change (1 : ℚ) ≤ I.n
      exact_mod_cast (show 1 ≤ I.n by omega))
    rw [one_mul] at h1
    unfold ηFL
    have : δ0 ^ 2 / 100 < lmpC * (1 - δ0) := by norm_num [δ0, lmpC]
    linarith
  have hfM : fhatFL (toRaw I) f ≤ (ctxFL (toRaw I) f).ip.fmax := by
    change fhatFL (toRaw I) f ≤ 4 * ((toRaw I).n : ℚ) * MFL (toRaw I) f
    have hM : fhatFL (toRaw I) f ≤ MFL (toRaw I) f := by
      unfold MFL
      have : 0 ≤ (toRaw I).dMaxQ / tFL (toRaw I) f := by
        have := Instance.dMax_pos hI
        rw [← Raw.dMaxQ_toRaw] at this
        have : (0 : ℚ) < (toRaw I).dMaxQ := by exact_mod_cast this
        exact div_nonneg this.le ht.le
      linarith
    have : (1 : ℚ) ≤ 4 * ((toRaw I).n : ℚ) := by
      change (1 : ℚ) ≤ 4 * (I.n : ℚ)
      linarith
    nlinarith
  -- CompleteSolution gives a `0`-valid solution
  obtain ⟨hsol, hok⟩ := Ctx.complete_sol hX hnη hfM le_rfl (H := []) (by simp)
    (by simp [Ctx.SolOK]) (fun p hp ↦ by simp [Ctx.decH] at hp)
  set C := ctxFL (toRaw I) f with hC
  set H := C.complete (fhatFL (toRaw I) f) [] with hH
  have hreg : ∀ a ∈ H.flatten, a.2 = 0 := fun a ha ↦
    ((C.complete_atoms _ [] a ha).resolve_left (by simp)).1
  have hnr := Ctx.one_le_nRegA_of_sol hX hsol hreg
  obtain ⟨hne, hnd, hlt, hlen⟩ := Ctx.toCenters_spec hX hok hnr
  have hcost := Ctx.coreCost_toCenters_le hX hsol hok
  have hcore := coreCost_ctxFL (f := f) hne hlt ht
  -- the robust LMP guarantee with slack `0`
  set P' : Par := { C.par with η := 0 } with hP'
  have hP'g : P'.Good I.n := by
    have hg := hX.good
    refine ⟨hg.δ_pos, hg.δ_le, hg.ε_pos, hg.ε_le, le_rfl, ?_, hg.K_ge⟩
    change (I.n : ℚ) * 0 ≤ C.par.δ * C.par.ε / 10
    have := hg.δ_pos
    have := hg.ε_pos
    rw [mul_zero]
    positivity
  have hsol' : Sol P' (scSpace I hI _ ht).d (fhatFL (toRaw I) f) P'.η (Ctx.decH hX H) :=
    sol_eta hsol 0
  have hf' : (I.n : ℚ) * P'.η < fhatFL (toRaw I) f := by
    change (I.n : ℚ) * 0 < _
    rw [mul_zero]
    linarith [hfh1, show (0 : ℚ) < lmpC * (1 - δ0) by norm_num [lmpC, δ0]]
  have hlmp := robust_lmp (scSpace I hI _ ht) P' hP'g hX.d1 hf' hsol' O hO
  have hconn : connCost P' (scSpace I hI _ ht).d (Ctx.decH hX H) =
      connCost C.par (scSpace I hI _ ht).d (Ctx.decH hX H) := rfl
  rw [hconn, costF_scSpace hO, ← hco_def] at hlmp
  -- the number of facilities
  have hlenS : ((toCenters H).length : ℚ) ≤ (nReg (Ctx.decH hX H) : ℚ) := by
    have h1 : nRegA H = H.flatten.length := by
      unfold nRegA
      rw [List.filter_eq_self.2 fun a ha ↦ by simp [hreg a ha]]
    have h2 := Ctx.nRegA_eq hX H
    exact_mod_cast hlen.trans (h1.symm.trans h2).le
  have hnt : (I.n : ℚ) * tFL (toRaw I) f ≤ dminFL (toRaw I) / cS := by
    have h1 : tFL (toRaw I) f ≤ dminFL (toRaw I) / (cS * I.n) := min_le_left _ _
    have h2 := mul_le_mul_of_nonneg_left h1 hn0.le
    have e : (I.n : ℚ) * (dminFL (toRaw I) / (cS * I.n)) = dminFL (toRaw I) / cS := by
      field_simp
    linarith
  have hδP : P'.δ = δ0 := rfl
  rw [hδP] at hlmp
  have key := fl_arith ht hf.le rfl (hcore ▸ hcost) rfl hlenS hnt hdm_pos hdm_le hlmp
  refine ⟨⟨hne, hnd, hlt⟩, ?_⟩
  have hkey : ((score (toRaw I) f (toCenters H) : ℚ) : ℝ) ≤
      ((lmpC * (co + f * O.card) : ℚ) : ℝ) := by
    exact_mod_cast key
  rw [← hco]
  push_cast at hkey
  exact hkey

end BCFGJPSSV26.FL
