module

public import Background.Tuples
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Tuples in a ball, cut at a budget

The grid of the greedy net (`BHSV25/Net/GSMachine.lean`) is the set of integer vectors
`m ∈ {-N, …, N}^T` with `∑ m_l² ≤ N²`, written as tuples over `{0, …, 2N}` shifted by `N`.
There are at most `(3 (1 + 2 S / T))^T` of them, `S = ⌊√(T N²)⌋` (`BHSV25.Net.ballCount_le`),
against `(2N + 1)^T` for the whole cube: for `N = (⌊√T⌋ + 1) K` the bound is `(3 + 12 K)^T`
(`BHSV25.Net.ballBudget_sqrt`), exponential in `T` instead of `T^{Θ(T)}`.

* **The enumeration** (`BHSV25.Net.ballTuples`): one coordinate at a time, keeping the tuples in
  the ball and at most `L` of them. The ball is closed under removing a coordinate, so when the
  budget `L` covers the numbers of tuples of every length up to `T` (`BHSV25.Net.BallBudget`),
  nothing is cut and every tuple of the ball appears (`BHSV25.Net.mem_ballTuples`).
* **The count**: `∑ |m_l| ≤ √(T ∑ m_l²) ≤ S` by Cauchy–Schwarz, so for `x ∈ (0, 1)` the count
  times `x^S` is at most `∑_m x^(∑ |m_l|) = (∑_(|j| ≤ N) x^|j|)^T ≤ ((1 + x) / (1 - x))^T`; take
  `x = S / (S + T)`.
-/

@[expose] public section

namespace BHSV25

namespace Net

open Tuples

/-! ### The enumeration -/

/-- The squared distance `∑ (m - N)²` of a tuple from the center `(N, …, N)`. -/
def offSq (N : ℕ) (q : List ℕ) : ℚ := (q.map fun m : ℕ ↦ ((m : ℚ) - N) ^ 2).sum

/-- The tuple is in the ball: `∑ (m - N)² ≤ N²`. -/
def inBall (N : ℕ) (q : List ℕ) : Bool := decide (offSq N q ≤ (N : ℚ) ^ 2)

/-- One more coordinate, keeping the tuples of the ball, cut at `L` tuples. -/
def ballStep (L N : ℕ) (l : List (List ℕ)) : List (List ℕ) :=
  ((tupleStepFull (2 * N + 1) l).filter (inBall N)).take L

/-- The `T`-tuples over `{0, …, 2N}` in the ball `∑ (m - N)² ≤ N²`, cut at `L` at every step. -/
def ballTuples (L N T : ℕ) : List (List ℕ) := (ballStep L N)^[T] [[]]

/-- The number of `i`-tuples over `{0, …, 2N}` in the ball. -/
def ballCount (N i : ℕ) : ℕ := (((tupleStepFull (2 * N + 1))^[i] [[]]).filter (inBall N)).length

/-- **The budget covers the ball**: at most `L` tuples of each length up to `T`. -/
def BallBudget (N T L : ℕ) : Prop := ∀ i ≤ T, ballCount N i ≤ L

theorem offSq_cons (N m : ℕ) (q : List ℕ) : offSq N (m :: q) = ((m : ℚ) - N) ^ 2 + offSq N q := by
  simp [offSq]

theorem offSq_nonneg (N : ℕ) (q : List ℕ) : 0 ≤ offSq N q := by
  induction q with
  | nil => simp [offSq]
  | cons m q ih => rw [offSq_cons]; positivity

theorem inBall_nil (N : ℕ) : inBall N [] = true := by
  simp [inBall, offSq]

theorem inBall_of_cons {N m : ℕ} {q : List ℕ} (h : inBall N (m :: q) = true) :
    inBall N q = true := by
  simp only [inBall, decide_eq_true_eq, offSq_cons] at h ⊢
  nlinarith [sq_nonneg ((m : ℚ) - N)]

/-- Filtering after one step only needs the tuples of the ball. -/
theorem filter_full_filter (N : ℕ) (l : List (List ℕ)) :
    (tupleStepFull (2 * N + 1) (l.filter (inBall N))).filter (inBall N) =
      (tupleStepFull (2 * N + 1) l).filter (inBall N) := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    unfold tupleStepFull at ih ⊢
    by_cases hq : inBall N q = true
    · rw [List.filter_cons_of_pos hq, List.flatMap_cons, List.flatMap_cons, List.filter_append,
        List.filter_append, ih]
    · rw [List.filter_cons_of_neg hq, List.flatMap_cons, List.filter_append, ih]
      have h0 : ((List.range (2 * N + 1)).map (· :: q)).filter (inBall N) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        obtain ⟨m, -, rfl⟩ := List.mem_map.1 ha
        exact fun h ↦ hq (inBall_of_cons h)
      rw [h0, List.nil_append]

/-- **Nothing is cut** when the budget covers the ball. -/
theorem ballTuples_eq {L N T : ℕ} (h : BallBudget N T L) :
    ballTuples L N T = ((tupleStepFull (2 * N + 1))^[T] [[]]).filter (inBall N) := by
  suffices ∀ i ≤ T, (ballStep L N)^[i] [[]] =
      ((tupleStepFull (2 * N + 1))^[i] [[]]).filter (inBall N) from this T le_rfl
  intro i hi
  induction i with
  | zero => simp [inBall_nil]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega), ballStep, filter_full_filter,
      ← Function.iterate_succ_apply' (tupleStepFull (2 * N + 1))]
    exact List.take_of_length_le (h (i + 1) hi)

theorem mem_ballTuples {L N T : ℕ} (h : BallBudget N T L) {q : List ℕ} :
    q ∈ ballTuples L N T ↔
      (q.length = T ∧ ∀ x ∈ q, x < 2 * N + 1) ∧ offSq N q ≤ (N : ℚ) ^ 2 := by
  rw [ballTuples_eq h, List.mem_filter, mem_iterate_tupleStepFull]
  simp [inBall]

theorem offSq_ofFn (N : ℕ) {T : ℕ} (f : Fin T → ℕ) :
    offSq N (List.ofFn f) = ∑ i, ((f i : ℚ) - N) ^ 2 := by
  rw [offSq, List.map_ofFn, List.sum_ofFn]
  rfl

theorem ofFn_mem_ballTuples {L N T : ℕ} (h : BallBudget N T L) (f : Fin T → Fin (2 * N + 1))
    (hf : ∑ i, (((f i : ℕ) : ℚ) - N) ^ 2 ≤ (N : ℚ) ^ 2) :
    List.ofFn (fun i ↦ (f i : ℕ)) ∈ ballTuples L N T := by
  rw [mem_ballTuples h, offSq_ofFn]
  refine ⟨⟨by simp, fun x hx ↦ ?_⟩, hf⟩
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  exact (f j).2

theorem BallBudget.mono {N T L T' : ℕ} (h : BallBudget N T L) (hT : T' ≤ T) :
    BallBudget N T' L :=
  fun i hi ↦ h i (hi.trans hT)

/-- The states of the loop: at most `L` tuples, of at most `i` entries below `2N + 1`. -/
theorem ballTuples_iter_small (L N i : ℕ) :
    (∀ q ∈ (ballStep L N)^[i] [[]], q.length ≤ i ∧ ∀ a ∈ q, a < 2 * N + 1) ∧
      ((ballStep L N)^[i] [[]]).length ≤ L + 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨fun q hq ↦ ?_, ?_⟩
    · have hq' := List.mem_of_mem_filter (List.mem_of_mem_take hq)
      simp only [tupleStepFull, List.mem_flatMap, List.mem_map, List.mem_range] at hq'
      obtain ⟨q', hq', a, ha, rfl⟩ := hq'
      obtain ⟨h1, h2⟩ := ih.1 q' hq'
      refine ⟨by simp; omega, fun b hb ↦ ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact h2 b hb
    · rw [ballStep, List.length_take]
      omega

/-! ### The count -/

/-- The `ℓ¹` distance `∑ |m - N|` from the center. -/
def offAbs (N : ℕ) (q : List ℕ) : ℕ := (q.map fun m ↦ m - N + (N - m)).sum

theorem cast_dist (m N : ℕ) : ((m - N + (N - m) : ℕ) : ℝ) = |(m : ℝ) - N| := by
  rcases le_total m N with h | h
  · have h' : (m : ℝ) ≤ N := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_of_nonpos (by linarith), neg_sub]
  · have h' : (N : ℝ) ≤ m := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg (by linarith)]

theorem offAbs_cons (N m : ℕ) (q : List ℕ) :
    offAbs N (m :: q) = (m - N + (N - m)) + offAbs N q := by
  simp [offAbs]

/-- **Cauchy–Schwarz**: `(∑ |m - N|)² ≤ len · ∑ (m - N)²`. -/
theorem offAbs_sq_le (N : ℕ) (q : List ℕ) :
    ((offAbs N q : ℕ) : ℝ) ^ 2 ≤ q.length * ((offSq N q : ℚ) : ℝ) := by
  induction q with
  | nil => simp [offAbs, offSq]
  | cons m q ih =>
    rw [offAbs_cons, offSq_cons, List.length_cons, Nat.cast_add, cast_dist]
    push_cast
    set a := |(m : ℝ) - N| with ha
    set F := ((offAbs N q : ℕ) : ℝ)
    set G := ((offSq N q : ℚ) : ℝ) with hG
    set k := (q.length : ℝ)
    have ha2 : ((m : ℝ) - N) ^ 2 = a ^ 2 := (sq_abs _).symm
    rw [ha2]
    have ha0 : 0 ≤ a := abs_nonneg _
    have hF0 : 0 ≤ F := Nat.cast_nonneg _
    have hG0 : 0 ≤ G := by rw [hG]; exact_mod_cast offSq_nonneg N q
    have hk0 : 0 ≤ k := Nat.cast_nonneg _
    have hX : 0 ≤ k * a ^ 2 + G - 2 * a * F := by
      rcases hk0.lt_or_eq with hk | hk
      · have : 0 ≤ k * (k * a ^ 2 + G - 2 * a * F) := by nlinarith [sq_nonneg (k * a - F)]
        exact nonneg_of_mul_nonneg_right (by linarith) hk
      · rw [← hk] at ih
        have hF : F = 0 := by nlinarith
        rw [hF, ← hk]
        linarith
    nlinarith

/-- **The generating function**: `∑_q x^(∑ |q_l - N|) = (∑_(m ≤ 2N) x^|m - N|)^i`. -/
theorem sum_pow_offAbs (N : ℕ) (x : ℝ) (i : ℕ) :
    (((tupleStepFull (2 * N + 1))^[i] [[]]).map fun q ↦ x ^ offAbs N q).sum =
      (((List.range (2 * N + 1)).map fun m ↦ x ^ (m - N + (N - m))).sum) ^ i := by
  induction i with
  | zero => simp [offAbs]
  | succ i ih =>
    rw [Function.iterate_succ_apply', tupleStepFull, List.map_flatMap, List.flatMap_def,
      List.sum_flatten, List.map_map, pow_succ', ← ih, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun q _ ↦ ?_
    simp only [Function.comp_apply]
    rw [List.map_map, ← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left fun m _ ↦ ?_
    simp only [Function.comp_apply, offAbs_cons, pow_add]

theorem sum_map_range_finset {β : Type*} [AddCommMonoid β] (n : ℕ) (f : ℕ → β) :
    ((List.range n).map f).sum = ∑ m ∈ Finset.range n, f m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- `∑_(m ≤ 2N) x^|m - N| ≤ (1 + x) / (1 - x)` for `x ∈ [0, 1)`. -/
theorem sum_range_pow_dist_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    ((List.range (2 * N + 1)).map fun m ↦ x ^ (m - N + (N - m))).sum ≤ (1 + x) / (1 - x) := by
  rw [sum_map_range_finset]
  have hsplit : 2 * N + 1 = N + (N + 1) := by ring
  rw [hsplit, Finset.sum_range_add]
  have h1 : ∑ m ∈ Finset.range N, x ^ (m - N + (N - m)) = x * ∑ m ∈ Finset.range N, x ^ m := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hm' := Finset.mem_range.1 hm
    rw [← pow_succ']
    congr 1
    omega
  have h2 : ∑ j ∈ Finset.range (N + 1), x ^ (N + j - N + (N - (N + j))) =
      ∑ j ∈ Finset.range (N + 1), x ^ j := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    omega
  rw [h1, h2]
  have hg : ∀ K, ∑ m ∈ Finset.range K, x ^ m ≤ 1 / (1 - x) := by
    intro K
    rw [geom_sum_eq hx1.ne, le_div_iff₀ (by linarith)]
    have : 0 ≤ x ^ K := pow_nonneg hx0 K
    rw [div_mul_eq_mul_div, div_le_iff_of_neg (by linarith)]
    nlinarith
  have hA := mul_le_mul_of_nonneg_left (hg N) hx0
  have hB := hg (N + 1)
  have e : x * (1 / (1 - x)) + 1 / (1 - x) = (1 + x) / (1 - x) := by
    field_simp
    ring
  linarith

/-- **The number of tuples in the ball**: for `i ≤ T`, at most `(3 (1 + 2 S / T))^T` tuples of
length `i`, `S = ⌊√(T N²)⌋`. -/
theorem ballCount_le {N T i : ℕ} (hi : i ≤ T) :
    (ballCount N i : ℝ) ≤ (3 * (1 + 2 * (Nat.sqrt (T * N ^ 2) : ℝ) / T)) ^ T := by
  set S := Nat.sqrt (T * N ^ 2) with hS
  set L := (tupleStepFull (2 * N + 1))^[i] [[]] with hL
  -- the tuples of the ball are close to the center in `ℓ¹`
  have habs : ∀ q ∈ L.filter (inBall N), offAbs N q ≤ S := by
    intro q hq
    obtain ⟨hqL, hqb⟩ := List.mem_filter.1 hq
    have hlen := (mem_iterate_tupleStepFull.1 hqL).1
    have hb : offSq N q ≤ (N : ℚ) ^ 2 := by simpa [inBall] using hqb
    have h1 := offAbs_sq_le N q
    rw [hlen] at h1
    have hb' : ((offSq N q : ℚ) : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hb
    have h2 : ((offAbs N q : ℕ) : ℝ) ^ 2 ≤ ((T * N ^ 2 : ℕ) : ℝ) := by
      push_cast
      have hiT : (i : ℝ) ≤ T := by exact_mod_cast hi
      have := offSq_nonneg N q
      have hq0 : (0 : ℝ) ≤ ((offSq N q : ℚ) : ℝ) := by exact_mod_cast this
      nlinarith
    have h3 : offAbs N q ^ 2 ≤ T * N ^ 2 := by exact_mod_cast h2
    exact Nat.le_sqrt'.2 h3
  -- for every `x ∈ (0, 1)`
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      (ballCount N i : ℝ) * x ^ S ≤ ((1 + x) / (1 - x)) ^ T := by
    intro x hx0 hx1
    have hc0 : 0 ≤ ((List.range (2 * N + 1)).map fun m ↦ x ^ (m - N + (N - m))).sum :=
      List.sum_nonneg fun a ha ↦ by
        obtain ⟨m, -, rfl⟩ := List.mem_map.1 ha
        positivity
    have hr1 : 1 ≤ (1 + x) / (1 - x) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hsub : ((L.filter (inBall N)).map fun q ↦ x ^ offAbs N q).sum ≤
        (L.map fun q ↦ x ^ offAbs N q).sum :=
      ((List.filter_sublist (l := L)).map _).sum_le_sum fun a ha ↦ by
        obtain ⟨q, -, rfl⟩ := List.mem_map.1 ha
        positivity
    have hlow : (ballCount N i : ℝ) * x ^ S ≤
        ((L.filter (inBall N)).map fun q ↦ x ^ offAbs N q).sum := by
      have h := List.length_nsmul_le_sum ((L.filter (inBall N)).map fun q ↦ x ^ offAbs N q)
        (x ^ S) (fun a ha ↦ by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
          exact pow_le_pow_of_le_one hx0.le hx1.le (habs q hq))
      rw [List.length_map, nsmul_eq_mul] at h
      exact h
    calc (ballCount N i : ℝ) * x ^ S
        ≤ (L.map fun q ↦ x ^ offAbs N q).sum := hlow.trans hsub
      _ = (((List.range (2 * N + 1)).map fun m ↦ x ^ (m - N + (N - m))).sum) ^ i :=
          sum_pow_offAbs N x i
      _ ≤ ((1 + x) / (1 - x)) ^ i :=
          pow_le_pow_left₀ hc0 (sum_range_pow_dist_le hx0.le hx1 N) i
      _ ≤ ((1 + x) / (1 - x)) ^ T := pow_le_pow_right₀ hr1 hi
  rcases Nat.eq_zero_or_pos S with hS0 | hSpos
  · -- `S = 0`: take `x = 1/2`
    have h := key (1 / 2) (by norm_num) (by norm_num)
    rw [hS0, pow_zero, mul_one] at h
    rw [hS0, Nat.cast_zero, mul_zero, zero_div, add_zero, mul_one]
    convert h using 2
    norm_num
  · -- `x = S / (S + T)`
    have hT : 0 < T := by
      rcases Nat.eq_zero_or_pos T with h | h
      · rw [hS, h, zero_mul, Nat.sqrt_zero] at hSpos
        exact absurd hSpos (lt_irrefl 0)
      · exact h
    have hS' : (0 : ℝ) < S := by exact_mod_cast hSpos
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    set x : ℝ := S / (S + T) with hx
    have hx0 : 0 < x := by positivity
    have hx1 : x < 1 := by rw [hx, div_lt_one (by positivity)]; linarith
    have h := key x hx0 hx1
    have hratio : (1 + x) / (1 - x) = 1 + 2 * S / T := by
      have hTne : (T : ℝ) ≠ 0 := hT'.ne'
      have hSTne : (S : ℝ) + T ≠ 0 := by positivity
      have h2 : 1 - (S : ℝ) / (S + T) = T / (S + T) := by field_simp; ring
      rw [hx, h2, div_div_eq_mul_div, add_mul, one_mul, div_mul_cancel₀ _ hSTne]
      field_simp
      ring
    have hinv : (1 / x) ^ S ≤ (3 : ℝ) ^ T := by
      have e : 1 / x = 1 + T / S := by rw [hx]; field_simp
      rw [e]
      calc (1 + (T : ℝ) / S) ^ S ≤ Real.exp ((T : ℝ) / S) ^ S := by
            refine pow_le_pow_left₀ (by positivity) ?_ S
            linarith [Real.add_one_le_exp ((T : ℝ) / S)]
        _ = Real.exp T := by
            rw [← Real.exp_nat_mul]
            congr 1
            field_simp
        _ = Real.exp 1 ^ T := by rw [← Real.exp_nat_mul, mul_one]
        _ ≤ 3 ^ T := by
            refine pow_le_pow_left₀ (Real.exp_pos 1).le ?_ T
            exact Real.exp_one_lt_three.le
    have hxS : 0 < x ^ S := pow_pos hx0 S
    rw [hratio] at h
    have h1 : (ballCount N i : ℝ) ≤ (1 + 2 * S / T) ^ T * (1 / x) ^ S := by
      rw [one_div_pow, ← div_eq_mul_one_div, le_div_iff₀ hxS]
      exact h
    calc (ballCount N i : ℝ) ≤ (1 + 2 * S / T) ^ T * (1 / x) ^ S := h1
      _ ≤ (1 + 2 * S / T) ^ T * 3 ^ T :=
          mul_le_mul_of_nonneg_left hinv (pow_nonneg (by positivity) T)
      _ = (3 * (1 + 2 * (S : ℝ) / T)) ^ T := by rw [mul_pow, mul_comm]

/-- **The budget `(3 + 12 K)^T` covers the ball** of radius `N = (⌊√T⌋ + 1) K`. -/
theorem ballBudget_sqrt (T K : ℕ) :
    BallBudget ((Nat.sqrt T + 1) * K) T ((3 + 12 * K) ^ T) := by
  intro i hi
  set N := (Nat.sqrt T + 1) * K with hN
  have h := ballCount_le (N := N) hi
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    have hi0 : i = 0 := by omega
    subst hi0
    simp [ballCount, inBall_nil]
  -- `S ≤ 2 T K`
  have hs1 : 1 ≤ Nat.sqrt T := Nat.sqrt_pos.2 hT
  have hs2 : Nat.sqrt T ^ 2 ≤ T := Nat.sqrt_le' T
  have hSle : Nat.sqrt (T * N ^ 2) ≤ 2 * T * K := by
    have h1 : T * N ^ 2 ≤ (2 * T * K) ^ 2 := by
      have h2 : (Nat.sqrt T + 1) ^ 2 ≤ 4 * T := by nlinarith
      calc T * N ^ 2 = T * ((Nat.sqrt T + 1) ^ 2 * K ^ 2) := by rw [hN]; ring
        _ ≤ T * (4 * T * K ^ 2) := by gcongr
        _ = (2 * T * K) ^ 2 := by ring
    calc Nat.sqrt (T * N ^ 2) ≤ Nat.sqrt ((2 * T * K) ^ 2) := Nat.sqrt_le_sqrt h1
      _ = 2 * T * K := Nat.sqrt_eq' _
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hS' : (Nat.sqrt (T * N ^ 2) : ℝ) ≤ 2 * T * K := by exact_mod_cast hSle
  have hbase : 3 * (1 + 2 * (Nat.sqrt (T * N ^ 2) : ℝ) / T) ≤ 3 + 12 * K := by
    have : 2 * (Nat.sqrt (T * N ^ 2) : ℝ) / T ≤ 4 * K := by
      rw [div_le_iff₀ hT']
      linarith
    linarith
  have h2 : (ballCount N i : ℝ) ≤ ((3 + 12 * K : ℕ) : ℝ) ^ T := by
    refine h.trans (pow_le_pow_left₀ (by positivity) ?_ T)
    push_cast
    exact hbase
  exact_mod_cast h2

end Net

end BHSV25
