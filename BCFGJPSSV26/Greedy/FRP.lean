module

public import BCFGJPSSV26.Greedy.Bid
public import KMedian195.Main
public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Fin.Basic

/-!
# The factor-revealing program

The bound on the factor-revealing program of [BCFGJPSSV26a, Definition 4.1, Theorem 4.4] at
`γ = 153/125`, in the form the analysis uses: unnormalized, over the rationals, and over any
finite linear order of clients (`BCFGJPSSV26.Greedy.FRP.boundOn`).

The bound itself is `KMedian195.originalPrimalUpperBound_exact` (copied from
`epfl-thl2/project-k-median`), for the program `KMedian195.OriginalPrimalSolution.Feasible` with
`∑ d = 1`, real variables and clients `Fin n`. Here:

* `BCFGJPSSV26.Greedy.FRP.FeasibleFin` is the same set of constraints without the normalization,
  over `ℚ`, and `BCFGJPSSV26.Greedy.FRP.boundFin` is the bound `obj ≤ f + ρ ∑ d`, by dividing by
  `∑ d`, casting to `ℝ` and applying `KMedian195.originalPrimalUpperBound_exact`.
* `BCFGJPSSV26.Greedy.FRP.FeasibleOn` is the program over a finite linear order `ι`, with the
  times `ι ∪ {⊤}` as `WithTop ι` and the successor of `k` as `BCFGJPSSV26.Greedy.FRP.nxt k`. Its
  metric constraint is asked for all `j, l` (the paper's only for `j ≠ l`; for `j = l` it is
  trivial), and its facility constraint is split in two sums. `BCFGJPSSV26.Greedy.FRP.boundOn`
  transports it to `Fin n` along the order isomorphism `ι ≃o Fin n`.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy.FRP

open Finset

/-! ### Over `Fin n` -/

/-- The factor-revealing program of `KMedian195.OriginalPrimalSolution.Feasible`, without the
normalization `∑ d = 1`, over `ℚ`: clients `Fin n`, times `Fin (n + 1)`. -/
structure FeasibleFin (n : ℕ) (r : Fin n → Fin (n + 1) → ℚ) (d : Fin n → ℚ) (f : ℚ) : Prop where
  mono : ∀ j i : Fin n, j ≤ i → r j i.succ ≤ r j i.castSucc
  tri : ∀ j k : Fin n, j < k → r k k.castSucc ≤ r j k.castSucc + d k + d j
  metric : ∀ (j k : Fin n) (ℓ : Fin (n + 1)), j ≠ k → j.castSucc < ℓ → k.castSucc < ℓ →
    r j ℓ ≤ r k ℓ + d k + d j
  facility : ∀ k : Fin n,
    (∑ j, if j < k then bid (r j k.castSucc) (d j) else bid (r k k.castSucc) (d j)) ≤ f
  f_nonneg : 0 ≤ f
  d_nonneg : ∀ j, 0 ≤ d j
  r_nonneg : ∀ j ℓ, 0 ≤ r j ℓ

/-- The objective of the factor-revealing program, without the opening cost. -/
def objFin (n : ℕ) (r : Fin n → Fin (n + 1) → ℚ) : ℚ :=
  ∑ j : Fin n, ((∑ i ∈ univ.filter (j ≤ ·), bid (r j i.castSucc) (r j i.succ)) + r j (Fin.last n))

/-- `KMedian195`'s bid at `γ = 153/125`, at rational arguments, is the cast of `bid`. -/
theorem bidValue_ratCast (x y : ℚ) :
    KMedian195.OriginalPrimalSolution.bidValue (153 / 125) (x : ℝ) (y : ℝ) = (bid x y : ℝ) := by
  simp only [KMedian195.OriginalPrimalSolution.bidValue, bid, γ]
  push_cast
  rfl

/-- The bound for `∑ d = 1`: the program cast to `ℝ` is `KMedian195`'s. -/
theorem boundFin_one {n : ℕ} {r : Fin n → Fin (n + 1) → ℚ} {d : Fin n → ℚ} {f : ℚ}
    (h : FeasibleFin n r d f) (hd : ∑ j, d j = 1) : objFin n r ≤ f + ρ := by
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hd
  have hb := KMedian195.originalPrimalUpperBound_exact (153 / 125) (by norm_num) le_rfl n hn
    ⟨fun j ↦ (d j : ℝ), (f : ℝ), fun j ℓ ↦ (r j ℓ : ℝ)⟩ ?_
  · have hobj : KMedian195.OriginalPrimalSolution.objective (153 / 125)
        ⟨fun j ↦ (d j : ℝ), (f : ℝ), fun j ℓ ↦ (r j ℓ : ℝ)⟩ = ((objFin n r - f : ℚ) : ℝ) := by
      simp only [KMedian195.OriginalPrimalSolution.objective, bidValue_ratCast, objFin,
        KMedian195.suffixRange, KMedian195.TimeIdx.ofIdx, KMedian195.TimeIdx.succ,
        KMedian195.TimeIdx.last]
      push_cast
      rfl
    have hρ : (2 - ((153 : ℝ) / 125 - 1) ^ 2) = (ρ : ℝ) := by
      simp only [ρ, γ]
      push_cast
      rfl
    rw [hobj, hρ] at hb
    have : objFin n r - f ≤ ρ := by exact_mod_cast hb
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp only [KMedian195.TimeIdx.ofIdx, KMedian195.TimeIdx.succ]
  · exact_mod_cast hd
  · intro j i hji
    exact_mod_cast h.mono j i hji
  · intro j k hjk
    exact_mod_cast h.tri j k hjk
  · intro j k ℓ hjk hj hk
    exact_mod_cast h.metric j k ℓ hjk hj hk
  · intro k
    have hk := (Rat.cast_le (K := ℝ)).mpr (h.facility k)
    push_cast [apply_ite (Rat.cast : ℚ → ℝ)] at hk
    simpa only [dite_eq_ite, bidValue_ratCast] using hk
  · exact_mod_cast h.f_nonneg
  · intro j
    exact_mod_cast h.d_nonneg j
  · intro j ℓ
    exact_mod_cast h.r_nonneg j ℓ

/-- The program is invariant under scaling by `c > 0`. -/
theorem FeasibleFin.smul {n : ℕ} {r : Fin n → Fin (n + 1) → ℚ} {d : Fin n → ℚ} {f : ℚ}
    (h : FeasibleFin n r d f) {c : ℚ} (hc : 0 < c) :
    FeasibleFin n (fun j ℓ ↦ c * r j ℓ) (fun j ↦ c * d j) (c * f) where
  mono j i hji := mul_le_mul_of_nonneg_left (h.mono j i hji) hc.le
  tri j k hjk := (mul_le_mul_of_nonneg_left (h.tri j k hjk) hc.le).trans_eq (by ring)
  metric j k ℓ hjk hj hk :=
    (mul_le_mul_of_nonneg_left (h.metric j k ℓ hjk hj hk) hc.le).trans_eq (by ring)
  facility k := by
    simp only [bid_smul hc, ← mul_ite, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (h.facility k) hc.le
  f_nonneg := mul_nonneg hc.le h.f_nonneg
  d_nonneg j := mul_nonneg hc.le (h.d_nonneg j)
  r_nonneg j ℓ := mul_nonneg hc.le (h.r_nonneg j ℓ)

/-- The objective is homogeneous. -/
theorem objFin_smul (n : ℕ) (r : Fin n → Fin (n + 1) → ℚ) {c : ℚ} (hc : 0 < c) :
    objFin n (fun j ℓ ↦ c * r j ℓ) = c * objFin n r := by
  simp only [objFin, bid_smul hc, Finset.mul_sum, mul_add]

/-- **The bound on the factor-revealing program**, unnormalized: `obj ≤ f + ρ ∑ d`. From
`KMedian195.originalPrimalUpperBound_exact` at `γ = 153/125`, applied to `(r, d, f) / ∑ d`. -/
theorem boundFin {n : ℕ} {r : Fin n → Fin (n + 1) → ℚ} {d : Fin n → ℚ} {f : ℚ}
    (h : FeasibleFin n r d f) (hd : 0 < ∑ j, d j) : objFin n r ≤ f + ρ * ∑ j, d j := by
  set S := ∑ j, d j with hS
  have hc : 0 < S⁻¹ := inv_pos.mpr hd
  have h1 : ∑ j, S⁻¹ * d j = 1 := by
    rw [← Finset.mul_sum, ← hS, inv_mul_cancel₀ hd.ne']
  have hb := boundFin_one (h.smul hc) h1
  rw [objFin_smul n r hc] at hb
  have hb' := mul_le_mul_of_nonneg_left hb hd.le
  rw [mul_add, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul, one_mul] at hb'
  linarith

/-! ### Over a finite linear order -/

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The successor of `k` among the times `WithTop ι`: the next element of `ι`, or `⊤` for the
last one. -/
def nxt (k : ι) : WithTop ι := (univ.filter fun l ↦ k < l).min

/-- The factor-revealing program over a finite linear order `ι` of clients: `r j k` for times
`k : WithTop ι` (`⊤` is the paper's time `n + 1`), distances `d j` to the facility, and the
opening cost `f`. -/
structure FeasibleOn (r : ι → WithTop ι → ℚ) (d : ι → ℚ) (f : ℚ) : Prop where
  mono : ∀ j k : ι, j ≤ k → r j (nxt k) ≤ r j k
  tri : ∀ j k : ι, j < k → r k k ≤ r j k + d k + d j
  metric : ∀ (j l : ι) (k : WithTop ι), (j : WithTop ι) < k → (l : WithTop ι) < k →
    r j k ≤ r l k + d l + d j
  facility : ∀ k : ι, (∑ j ∈ univ.filter (· < k), bid (r j k) (d j)) +
    (∑ j ∈ univ.filter (k ≤ ·), bid (r k k) (d j)) ≤ f
  f_nonneg : 0 ≤ f
  d_nonneg : ∀ j, 0 ≤ d j
  r_nonneg : ∀ j k, 0 ≤ r j k

/-- The term of client `j` in the objective: `∑_{k ≥ j} β(r j k, r j (k + 1)) + r j ⊤`. -/
def term (r : ι → WithTop ι → ℚ) (j : ι) : ℚ :=
  (∑ k ∈ univ.filter (j ≤ ·), bid (r j k) (r j (nxt k))) + r j ⊤

theorem nxt_eq_coe {a b : ι} (hab : a < b) (h : ∀ c, a < c → b ≤ c) : nxt a = b :=
  le_antisymm (Finset.min_le (by simp [hab]))
    (Finset.le_min fun c hc ↦ WithTop.coe_le_coe.mpr (h c (by simpa using hc)))

theorem nxt_eq_top {a : ι} (h : ∀ c, ¬ a < c) : nxt a = ⊤ :=
  Finset.min_eq_top.mpr (Finset.filter_eq_empty_iff.mpr fun c _ ↦ h c)

/-- The times `Fin (n + 1)` as `WithTop ι`, along `e : Fin n ≃o ι`: `i.castSucc ↦ e i` and
`Fin.last n ↦ ⊤`. -/
def finTime {n : ℕ} (e : Fin n ≃o ι) (ℓ : Fin (n + 1)) : WithTop ι :=
  Fin.lastCases (motive := fun _ ↦ WithTop ι) ⊤ (fun i ↦ (e i : WithTop ι)) ℓ

section finTime

variable {n : ℕ} (e : Fin n ≃o ι)

omit [Fintype ι] in
@[simp] theorem finTime_castSucc (i : Fin n) : finTime e i.castSucc = e i := by
  simp [finTime]

omit [Fintype ι] in
@[simp] theorem finTime_last : finTime e (Fin.last n) = ⊤ := by
  simp [finTime]

@[simp] theorem finTime_succ (i : Fin n) : finTime e i.succ = nxt (e i) := by
  by_cases hi : (i : ℕ) + 1 < n
  · have : i.succ = (⟨i + 1, hi⟩ : Fin n).castSucc := Fin.ext (by simp)
    rw [this, finTime_castSucc]
    symm
    apply nxt_eq_coe
    · exact e.lt_iff_lt.mpr (Fin.lt_def.mpr (by simp))
    · intro c hc
      obtain ⟨m, rfl⟩ := e.surjective c
      rw [e.lt_iff_lt, Fin.lt_def] at hc
      rw [e.le_iff_le, Fin.le_def]
      simp only
      omega
  · have : i.succ = Fin.last n := Fin.ext (by simp; omega)
    rw [this, finTime_last]
    symm
    apply nxt_eq_top
    intro c hc
    obtain ⟨m, rfl⟩ := e.surjective c
    rw [e.lt_iff_lt, Fin.lt_def] at hc
    have := m.isLt
    omega

omit [Fintype ι] in
theorem lt_finTime {j : Fin n} {ℓ : Fin (n + 1)} (h : j.castSucc < ℓ) :
    (e j : WithTop ι) < finTime e ℓ := by
  induction ℓ using Fin.lastCases with
  | last => simp
  | cast l =>
    rw [finTime_castSucc, WithTop.coe_lt_coe, e.lt_iff_lt]
    exact Fin.castSucc_lt_castSucc_iff.mp h

end finTime

/-- The program over `ι` gives the program over `Fin n` along `e : Fin n ≃o ι`. -/
theorem FeasibleOn.fin {r : ι → WithTop ι → ℚ} {d : ι → ℚ} {f : ℚ} (h : FeasibleOn r d f)
    {n : ℕ} (e : Fin n ≃o ι) :
    FeasibleFin n (fun j ℓ ↦ r (e j) (finTime e ℓ)) (fun j ↦ d (e j)) f where
  mono j i hji := by
    simpa using h.mono (e j) (e i) (e.le_iff_le.mpr hji)
  tri j k hjk := by
    simpa using h.tri (e j) (e k) (e.lt_iff_lt.mpr hjk)
  metric j k ℓ _ hj hk := h.metric (e j) (e k) (finTime e ℓ) (lt_finTime e hj) (lt_finTime e hk)
  facility k := by
    simp only [finTime_castSucc]
    rw [Finset.sum_ite]
    refine le_of_eq_of_le ?_ (h.facility (e k))
    congr 1
    · exact Finset.sum_equiv e.toEquiv (by simp) (by simp)
    · exact Finset.sum_equiv e.toEquiv (by simp) (by simp)
  f_nonneg := h.f_nonneg
  d_nonneg j := h.d_nonneg (e j)
  r_nonneg j ℓ := h.r_nonneg (e j) (finTime e ℓ)

/-- The objective over `Fin n` along `e : Fin n ≃o ι` is `∑_j term j`. -/
theorem objFin_finTime (r : ι → WithTop ι → ℚ) {n : ℕ} (e : Fin n ≃o ι) :
    objFin n (fun j ℓ ↦ r (e j) (finTime e ℓ)) = ∑ j, term r j := by
  simp only [objFin, finTime_castSucc, finTime_succ, finTime_last, term]
  refine Fintype.sum_equiv e.toEquiv _ _ fun j ↦ ?_
  congr 1
  exact Finset.sum_equiv e.toEquiv (by simp) (by simp)

/-- **The bound on the factor-revealing program over a finite linear order**:
`∑_j term j ≤ f + ρ ∑ d`. From `BCFGJPSSV26.Greedy.FRP.boundFin` along `ι ≃o Fin n`. -/
theorem boundOn {r : ι → WithTop ι → ℚ} {d : ι → ℚ} {f : ℚ} (h : FeasibleOn r d f)
    (hd : 0 < ∑ j, d j) : ∑ j, term r j ≤ f + ρ * ∑ j, d j := by
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  have hsum : ∑ j, d (e j) = ∑ j, d j := e.toEquiv.sum_comp d
  have hb := boundFin (h.fin e) (by rwa [hsum])
  rwa [objFin_finTime, hsum] at hb

end BCFGJPSSV26.Greedy.FRP
