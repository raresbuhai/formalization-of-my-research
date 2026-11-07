module

public import BBKS24.GraphList
public import BBKS24.Statistic

/-!
# The algorithm

The algorithm of [BBKS24] (Algorithm 1, derandomized, with `p` unknown), on vertex numbers.

* **The test** (`BBKS24.Alg.selTest`). For a grid point `q = j/M` and the list `v :: α` (the
  vertex `v` and the triple `α`), the statistic `⟨Ḡ_α, Ḡ_v⟩` of `BBKS24.stat` is
  `∑ᵢ ∏_{t ∈ v :: α} χ(t ~ i)`, and `χ(b) = (x_b - q)/√(q(1-q))` with `x_b ∈ {0, 1}`. So the
  statistic only depends on the numbers `c_e` of rows `i` with `e` heads among the four factors,
  and `stat ≥ k p₊⁴ / 2` iff `2 (c₃ w³ j + c₁ w j³) + k w⁴ ≤ 2 (c₄ w⁴ + c₂ w² j² + c₀ j⁴)` with
  `w = M - j` (`BBKS24.Alg.selTest_iff`): natural numbers only.
-/

@[expose] public section

open Finset RandomGraph

namespace BBKS24.Alg

/-! ### Adjacency from the non-edges -/

/-- `u ~ v` or `u = v`, for the list `E` of non-edges. -/
def radjL (E : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  decide (u = v) || !decide ((min u v, max u v) ∈ E)

/-- `E` lists the non-edges of `G`: a pair `u < v` is in `E` iff it is not an edge. -/
def NonEdgesOf {n : ℕ} (G : SimpleGraph (Fin n)) (E : List (ℕ × ℕ)) : Prop :=
  ∀ u v : Fin n, u < v → ((((u : ℕ), (v : ℕ)) ∈ E) ↔ ¬ G.Adj u v)

theorem nonEdgesOf_nonEdges {n : ℕ} (G : SimpleGraph (Fin n)) :
    NonEdgesOf G (nonEdges n (adjBits G)) := by
  intro u v huv
  rw [mem_nonEdges]
  constructor
  · rintro ⟨u', v', h1, h2, _, hG⟩
    rwa [show u' = u from Fin.ext h1, show v' = v from Fin.ext h2] at hG
  · intro hG
    exact ⟨u, v, rfl, rfl, huv, hG⟩

theorem nonEdgesOf_nonEdgesAug {n b j : ℕ} (G : SimpleGraph (Fin n)) (r : List Bool) :
    NonEdgesOf (G ⊔ Sampling.chunkGraph n b j r) (nonEdgesAug n b j (adjBits G) r) := by
  intro u v huv
  rw [mem_nonEdgesAug]
  constructor
  · rintro ⟨u', v', h1, h2, _, hG⟩
    rwa [show u' = u from Fin.ext h1, show v' = v from Fin.ext h2] at hG
  · intro hG
    exact ⟨u, v, rfl, rfl, huv, hG⟩

open Classical in
theorem radjL_eq {n : ℕ} {G : SimpleGraph (Fin n)} {E : List (ℕ × ℕ)} (hE : NonEdgesOf G E)
    (u v : Fin n) : radjL E u v = decide (radj G u v) := by
  classical
  rw [Bool.eq_iff_iff, radjL, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, radj, Fin.val_inj]
  refine or_congr_right' fun huv ↦ ?_
  rcases lt_or_gt_of_ne huv with h | h
  · rw [min_eq_left (Fin.le_def.1 h.le), max_eq_right (Fin.le_def.1 h.le), hE u v h, not_not]
  · rw [min_eq_right (Fin.le_def.1 h.le), max_eq_left (Fin.le_def.1 h.le), hE v u h, not_not]
    exact ⟨fun h' ↦ h'.symm, fun h' ↦ h'.symm⟩

/-! ### The test -/

/-- The number of heads at the row `i`: the entries `t` of `l` with `t ~ i` or `t = i`. -/
def headCount (E : List (ℕ × ℕ)) (l : List ℕ) (i : ℕ) : ℕ := l.countP fun t ↦ radjL E t i

/-- The number of rows `i < n` with `e` heads. -/
def levelCount (n : ℕ) (E : List (ℕ × ℕ)) (l : List ℕ) (e : ℕ) : ℕ :=
  (List.range n).countP fun i ↦ decide (headCount E l i = e)

/-- **The test**, at the grid point `j/M`, for the list `l = v :: α`. -/
def selTest (n M j k : ℕ) (E : List (ℕ × ℕ)) (l : List ℕ) : Bool :=
  decide (2 * (levelCount n E l 3 * (M - j) ^ 3 * j + levelCount n E l 1 * (M - j) * j ^ 3) +
      k * (M - j) ^ 4 ≤
    2 * (levelCount n E l 4 * (M - j) ^ 4 + levelCount n E l 2 * (M - j) ^ 2 * j ^ 2 +
      levelCount n E l 0 * j ^ 4))

/-- The characters as `(x_b - q)/√(q(1-q))`. -/
theorem chi_eq {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (b : Prop) [Decidable b] :
    chi q b = (if b then 1 - q else -q) / √(q * (1 - q)) := by
  have h1 : 0 < 1 - q := by linarith
  have hs : 0 < √(q * (1 - q)) := Real.sqrt_pos.2 (by positivity)
  by_cases h : b
  · rw [chi_of h, ite_eq_left h, pplus, eq_div_iff hs.ne', ← Real.sqrt_mul (div_nonneg h1.le hq.le),
      show (1 - q) / q * (q * (1 - q)) = (1 - q) ^ 2 by field_simp, Real.sqrt_sq h1.le]
  · rw [chi_of_not h, ite_eq_right h, pminus, neg_div, neg_inj, eq_div_iff hs.ne',
      ← Real.sqrt_mul (div_nonneg hq.le h1.le),
      show q / (1 - q) * (q * (1 - q)) = q ^ 2 by field_simp, Real.sqrt_sq hq.le]

/-- The product of the characters over a list, by its number of heads. -/
theorem prod_chi_list {α : Type*} {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (P : α → Prop)
    [DecidablePred P] (l : List α) :
    (l.map fun t ↦ chi q (P t)).prod =
      (1 - q) ^ (l.countP fun t ↦ P t) * (-q) ^ (l.length - l.countP fun t ↦ P t) /
        √(q * (1 - q)) ^ l.length := by
  have hs : 0 < √(q * (1 - q)) := Real.sqrt_pos.2 (by nlinarith)
  induction l with
  | nil => simp
  | cons t l ih =>
    set c := l.countP fun t ↦ decide (P t) with hc
    have hle : c ≤ l.length := List.countP_le_length
    rw [List.map_cons, List.prod_cons, ih, chi_eq hq hq1, List.countP_cons, List.length_cons]
    by_cases h : P t
    · simp only [h, ite_true, decide_true]
      rw [show l.length + 1 - (c + 1) = l.length - c by omega]
      field_simp
      ring
    · simp only [h, ite_false, decide_false, Bool.false_eq_true, add_zero]
      rw [show l.length + 1 - c = l.length - c + 1 by omega]
      field_simp
      ring

/-- `List.countP` on `List.range n` as the size of a filter of `Finset.range n`. -/
theorem countP_range (p : ℕ → Bool) (n : ℕ) :
    (List.range n).countP p = ((Finset.range n).filter fun i ↦ p i = true).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases h : p n = true
    · rw [ite_eq_left_iff.2 fun h' ↦ absurd h h', card_insert_of_notMem (by simp)]
      simp [h]
    · rw [ite_eq_right_iff.2 fun h' ↦ absurd h' h]
      simp [h]

/-- A triple, or any list of vertices, as a set of `Fin n`. -/
noncomputable def toFinsetN (n : ℕ) (α : List ℕ) : Finset (Fin n) := vertexSet n α

open Classical in
/-- The statistic through the head counts: `⟨Ḡ_α, Ḡ_v⟩ = (1/s⁴) ∑ᵢ (1-q)^hᵢ (-q)^(4-hᵢ)` with
`s = √(q(1-q))` and `hᵢ` the heads of `v :: α` at the row `i`. -/
theorem stat_eq_sum {n : ℕ} {q : ℝ} (hq : 0 < q) (hq1 : q < 1) {G : SimpleGraph (Fin n)}
    {E : List (ℕ × ℕ)} (hE : NonEdgesOf G E) (v : Fin n) {α : List (Fin n)} (hα : α.Nodup)
    (h3 : α.length = 3) :
    stat q G α.toFinset v = (∑ i ∈ Finset.range n,
      (1 - q) ^ headCount E (v :: α.map Fin.val) i *
        (-q) ^ (4 - headCount E (v :: α.map Fin.val) i)) / √(q * (1 - q)) ^ 4 := by
  rw [stat, sum_div]
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦ (1 - q) ^ headCount E (v :: α.map Fin.val) i *
    (-q) ^ (4 - headCount E (v :: α.map Fin.val) i) / √(q * (1 - q)) ^ 4)]
  refine sum_congr rfl fun i _ ↦ ?_
  have hprod : (∏ a ∈ α.toFinset, chi q (radj G a i)) * chi q (radj G v i) =
      ((v :: α).map fun t ↦ chi q (radj G t i)).prod := by
    rw [List.prod_toFinset _ hα, List.map_cons, List.prod_cons, mul_comm]
  have hhead : headCount E (v :: α.map Fin.val) i = (v :: α).countP fun t ↦ radj G t i := by
    rw [headCount, ← List.map_cons, List.countP_map]
    refine List.countP_congr fun t _ ↦ ?_
    simp [radjL_eq hE t i]
  rw [hprod, prod_chi_list hq hq1, hhead, List.length_cons, h3]

/-- The counts of rows with `e` heads, as a sum. -/
theorem sum_range_headCount {n : ℕ} (E : List (ℕ × ℕ)) (l : List ℕ) (hl : l.length = 4)
    (F : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, F (headCount E l i) =
      ∑ e ∈ Finset.range 5, (levelCount n E l e : ℝ) * F e := by
  rw [← sum_fiberwise_of_maps_to (g := headCount E l) (t := Finset.range 5) fun i _ ↦ by
    have := List.countP_le_length (p := fun t ↦ radjL E t i) (l := l)
    rw [hl] at this
    exact mem_range.2 (by unfold headCount; omega)]
  refine sum_congr rfl fun e _ ↦ ?_
  rw [levelCount, countP_range, sum_congr rfl fun i hi ↦ by rw [(mem_filter.1 hi).2], sum_const,
    nsmul_eq_mul]
  simp

/-- **The test** is the comparison of the statistic with `k p₊⁴ / 2`, at the grid point
`q = j/M`, `0 < j < M`. -/
theorem selTest_iff {n M j k : ℕ} (hj0 : 0 < j) (hjM : j < M) {G : SimpleGraph (Fin n)}
    {E : List (ℕ × ℕ)} (hE : NonEdgesOf G E) (v : Fin n) {α : List (Fin n)} (hα : α.Nodup)
    (h3 : α.length = 3) :
    selTest n M j k E ((v : ℕ) :: α.map Fin.val) = true ↔
      (k : ℝ) * pplus ((j : ℝ) / M) ^ 4 / 2 ≤ stat ((j : ℝ) / M) G α.toFinset v := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
  have hjMR : (j : ℝ) < M := by exact_mod_cast hjM
  set q : ℝ := (j : ℝ) / M with hqdef
  have hq : 0 < q := div_pos hjR hM
  have hq1 : q < 1 := (div_lt_one hM).2 hjMR
  set l : List ℕ := (v : ℕ) :: α.map Fin.val with hl
  have hl4 : l.length = 4 := by simp [hl, h3]
  rw [stat_eq_sum hq hq1 hE v hα h3, ← hl,
    sum_range_headCount E l hl4 fun h ↦ (1 - q) ^ h * (-q) ^ (4 - h)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  set c : ℕ → ℝ := fun e ↦ (levelCount n E l e : ℝ) with hc
  -- `p₊⁴ = ((1-q)/q)²` and `s⁴ = (q (1-q))²`.
  have h1q : 0 < 1 - q := by linarith
  have hp4 : pplus q ^ 4 = ((1 - q) / q) ^ 2 := by
    rw [pplus, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (div_nonneg h1q.le hq.le)]
  have hs4 : √(q * (1 - q)) ^ 4 = (q * (1 - q)) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
  rw [hp4, hs4, selTest, decide_eq_true_eq]
  have hw : ((M - j : ℕ) : ℝ) = M - j := by rw [Nat.cast_sub hjM.le]
  rw [← Nat.cast_le (α := ℝ)]
  push_cast [hw]
  rw [le_div_iff₀ (by positivity)]
  have hq' : q * M = j := by rw [hqdef]; field_simp
  have h1q' : (1 - q) * M = M - j := by rw [sub_mul, hq']; ring
  norm_num
  obtain ⟨c0, hc0⟩ : ∃ c, c = (levelCount n E l 0 : ℝ) := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ c, c = (levelCount n E l 1 : ℝ) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c, c = (levelCount n E l 2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c, c = (levelCount n E l 3 : ℝ) := ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ c, c = (levelCount n E l 4 : ℝ) := ⟨_, rfl⟩
  rw [← hc0, ← hc1, ← hc2, ← hc3, ← hc4]
  have hM4 : (0 : ℝ) < 2 * M ^ 4 := by positivity
  have key : c0 * (-q) ^ 4 + c1 * ((1 - q) * (-q) ^ 3) + c2 * ((1 - q) ^ 2 * q ^ 2) +
        -(c3 * ((1 - q) ^ 3 * q)) + c4 * (1 - q) ^ 4 - k * ((1 - q) / q) ^ 2 / 2 * (q * (1 - q)) ^ 2
      = (2 * (c4 * (M - j) ^ 4 + c2 * (M - j) ^ 2 * j ^ 2 + c0 * j ^ 4) -
          (2 * (c3 * (M - j) ^ 3 * j + c1 * (M - j) * j ^ 3) + k * (M - j) ^ 4)) / (2 * M ^ 4) := by
    rw [hqdef]
    field_simp
    ring
  constructor
  · intro h
    have := div_nonneg (sub_nonneg.2 h) hM4.le
    linarith
  · intro h
    have hQ : 0 ≤ (2 * (c4 * (M - j) ^ 4 + c2 * (M - j) ^ 2 * j ^ 2 + c0 * j ^ 4) -
        (2 * (c3 * (M - j) ^ 3 * j + c1 * (M - j) * j ^ 3) + k * (M - j) ^ 4)) / (2 * M ^ 4) := by
      linarith
    have := mul_nonneg hQ hM4.le
    rw [div_mul_cancel₀ _ hM4.ne'] at this
    linarith

/-! ### Adjacency, refinement and selection on lists -/

/-- `u ~ v`, for the list `E` of non-edges. -/
def adjL (E : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  decide (u ≠ v) && !decide ((min u v, max u v) ∈ E)

open Classical in
theorem adjL_eq {n : ℕ} {G : SimpleGraph (Fin n)} {E : List (ℕ × ℕ)} (hE : NonEdgesOf G E)
    (u v : Fin n) : adjL E u v = decide (G.Adj u v) := by
  rw [Bool.eq_iff_iff, adjL, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, ne_eq, Fin.val_inj]
  by_cases huv : u = v
  · simp [huv]
  · simp only [huv, not_false_eq_true, true_and]
    rcases lt_or_gt_of_ne huv with h | h
    · rw [min_eq_left (Fin.le_def.1 h.le), max_eq_right (Fin.le_def.1 h.le), hE u v h, not_not]
    · rw [min_eq_right (Fin.le_def.1 h.le), max_eq_left (Fin.le_def.1 h.le), hE v u h, not_not]
      exact ⟨fun h' ↦ h'.symm, fun h' ↦ h'.symm⟩

/-- **The refinement** on lists: the entries of `T` with at least `k - 1` neighbours in `T`. -/
def refineL (k : ℕ) (E : List (ℕ × ℕ)) (T : List ℕ) : List ℕ :=
  T.filter fun v ↦ decide (k - 1 ≤ T.countP fun w ↦ adjL E v w)

/-- **The selected vertices** on lists. -/
def selectedL (n M j k : ℕ) (E : List (ℕ × ℕ)) (α : List ℕ) : List ℕ :=
  (List.range n).filter fun v ↦ selTest n M j k E (v :: α)

theorem good_filter {n : ℕ} {T : List ℕ} (h : Good n T) (p : ℕ → Bool) : Good n (T.filter p) :=
  ⟨h.1.filter p, fun i hi ↦ h.2 i (List.mem_filter.1 hi).1⟩

theorem good_selectedL (n M j k : ℕ) (E : List (ℕ × ℕ)) (α : List ℕ) :
    Good n (selectedL n M j k E α) :=
  good_filter ⟨List.nodup_range, fun _ hi ↦ List.mem_range.1 hi⟩ _

theorem good_refineL {n k : ℕ} {E : List (ℕ × ℕ)} {T : List ℕ} (h : Good n T) :
    Good n (refineL k E T) :=
  good_filter h _

theorem mem_vertexSet {n : ℕ} {l : List ℕ} {v : Fin n} : v ∈ vertexSet n l ↔ (v : ℕ) ∈ l := by
  classical
  simp [vertexSet]

theorem vertexSet_refineL {n k : ℕ} {G : SimpleGraph (Fin n)} {E : List (ℕ × ℕ)}
    (hE : NonEdgesOf G E) {T : List ℕ} (hT : Good n T) :
    vertexSet n (refineL k E T) = refine G k (vertexSet n T) := by
  classical
  ext v
  rw [mem_vertexSet, refine, mem_filter, mem_vertexSet, refineL, List.mem_filter,
    decide_eq_true_eq]
  refine and_congr_right fun _ ↦ ?_
  have hfil : (vertexSet n T).filter (G.Adj v) = vertexSet n (T.filter fun w ↦ adjL E v w) := by
    ext w
    simp only [mem_filter, mem_vertexSet, List.mem_filter]
    rw [adjL_eq hE v w, decide_eq_true_eq]
  rw [hfil, card_vertexSet (good_filter hT _), List.countP_eq_length_filter]

open Classical in
theorem vertexSet_selectedL {n M j k : ℕ} (hj0 : 0 < j) (hjM : j < M) {G : SimpleGraph (Fin n)}
    {E : List (ℕ × ℕ)} (hE : NonEdgesOf G E) {α : List (Fin n)} (hα : α.Nodup)
    (h3 : α.length = 3) :
    vertexSet n (selectedL n M j k E (α.map Fin.val)) = selected ((j : ℝ) / M) G k α.toFinset := by
  ext v
  rw [mem_vertexSet, selectedL, List.mem_filter, selected, mem_filter]
  simp only [List.mem_range, v.2, true_and, mem_univ]
  exact selTest_iff hj0 hjM hE v hα h3

/-! ### The triples -/

/-- The triples `[a, b, c]`, `a < b < c < n`. -/
def triples (n : ℕ) : List (List ℕ) :=
  (List.range n).flatMap fun a ↦ ((List.range n).filter fun b ↦ decide (a < b)).flatMap fun b ↦
    ((List.range n).filter fun c ↦ decide (b < c)).map fun c ↦ [a, b, c]

/-- Every `3`-set of `Fin n` is listed, as an increasing triple. -/
theorem exists_mem_triples {n : ℕ} {α : Finset (Fin n)} (h3 : α.card = 3) :
    ∃ αL : List (Fin n), αL.Nodup ∧ αL.length = 3 ∧ αL.toFinset = α ∧
      αL.map Fin.val ∈ triples n := by
  refine ⟨α.sort (· ≤ ·), α.sort_nodup _, by rw [Finset.length_sort, h3], Finset.sort_toFinset _ _,
    ?_⟩
  have hs := Finset.pairwise_sort α (· ≤ ·)
  have hnd := α.sort_nodup (· ≤ ·)
  have hl : (α.sort (· ≤ ·)).length = 3 := by rw [Finset.length_sort, h3]
  match hm : α.sort (· ≤ ·), hl with
  | [a, b, c], _ =>
    rw [hm] at hs hnd
    simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true] at hs
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true] at hnd
    have hab : a < b := lt_of_le_of_ne hs.1.1 hnd.1.1
    have hbc : b < c := lt_of_le_of_ne hs.2 hnd.2
    simp only [triples, List.map_cons, List.map_nil, List.mem_flatMap, List.mem_range,
      List.mem_filter, decide_eq_true_eq, List.mem_map]
    exact ⟨a, a.2, b, ⟨b.2, hab⟩, c, ⟨c.2, hbc⟩, rfl⟩

/-! ### The algorithm -/

/-- `⌊log₂ n⌋ + 1`. -/
def logN (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- The bits per chunk, `b = 3 (⌊log₂ n⌋ + 1)`, so that `2^b > n³`. -/
def nBits (n : ℕ) : ℕ := 3 * logN n

/-- The grid size `M = 2^b`. -/
def gridM (n : ℕ) : ℕ := 2 ^ nBits n

/-- The pruning threshold `Δ = ⌊k² / (n L³)⌋ + 1`, `L = ⌊log₂ n⌋ + 1`. -/
def delta (n k : ℕ) : ℕ := k ^ 2 / (n * logN n ^ 3) + 1

/-- The candidates at the grid points `q = j/M ≥ 1/2`: the refined selected sets of all triples. -/
def candHigh (n k M : ℕ) (E : List (ℕ × ℕ)) : List (List ℕ) :=
  ((List.range M).filter fun j ↦ decide (M / 2 ≤ j)).flatMap fun j ↦
    (triples n).map fun t ↦ refineL k E (selectedL n M j k E t)

/-- The candidates after adding the pairs with chunks below `j ≤ M/2`, at `q = 1/2`. -/
def candLow (n k b M : ℕ) (a r : List Bool) : List (List ℕ) :=
  (List.range (M / 2 + 1)).flatMap fun j ↦
    (triples n).map fun t ↦
      refineL k (nonEdgesAug n b j a r) (selectedL n M (M / 2) k (nonEdgesAug n b j a r) t)

/-- The number of vertices, capped at one more than the number of adjacency bits. -/
def numV (x : Input) : ℕ := min x.1 (x.2.2.length + 1)

/-- **The algorithm**: the candidates of all grid points, cleaned up. -/
def alg (xr : Input × List Bool) : Output :=
  cleanupL xr.1.2.1 (delta (numV xr.1) xr.1.2.1) (nonEdges (numV xr.1) xr.1.2.2)
    (candHigh (numV xr.1) xr.1.2.1 (gridM (numV xr.1)) (nonEdges (numV xr.1) xr.1.2.2) ++
      candLow (numV xr.1) xr.1.2.1 (nBits (numV xr.1)) (gridM (numV xr.1)) xr.1.2.2 xr.2)

theorem numV_input {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : numV (input G k) = n :=
  min_eq_left (length_adjBits_ge G)

theorem two_le_gridM (n : ℕ) : 2 ≤ gridM n := by
  unfold gridM nBits logN
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ (3 * (Nat.log 2 n + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem gridM_half (n : ℕ) : ((gridM n / 2 : ℕ) : ℝ) / gridM n = 1 / 2 := by
  have h : gridM n = 2 * 2 ^ (nBits n - 1) := by
    unfold gridM
    rw [← pow_succ']
    congr 1
  rw [h, Nat.mul_div_cancel_left _ (by norm_num)]
  push_cast
  have : (0 : ℝ) < 2 ^ (nBits n - 1) := by positivity
  field_simp

theorem good_candidates (n k b M : ℕ) (E : List (ℕ × ℕ)) (a r : List Bool) :
    ∀ S ∈ candHigh n k M E ++ candLow n k b M a r, Good n S := by
  intro S hS
  simp only [candHigh, candLow, List.mem_append, List.mem_flatMap, List.mem_map] at hS
  rcases hS with ⟨j, _, t, _, rfl⟩ | ⟨j, _, t, _, rfl⟩
  · exact good_refineL (good_selectedL _ _ _ _ _ _)
  · exact good_refineL (good_selectedL _ _ _ _ _ _)

/-- **The specification of the algorithm** on the input of a graph `G`: its output consists of
`k`-cliques of `G`; it contains every `k`-clique `S` of `G` meeting the other `k`-cliques in fewer
than `Δ` vertices, if `S` is the refined set of a triple at some grid point `j/M ≥ 1/2`, or at
`1/2` after adding the pairs whose chunks of the coins are below some `j ≤ M/2`; and it has at
most `(n/k)(1 + 2nΔ/k²)` sets. -/
theorem alg_spec {n k : ℕ} (G : SimpleGraph (Fin n)) (r : List Bool) :
    (∀ l ∈ alg (input G k, r), G.IsNClique k (vertexSet n l)) ∧
    (∀ S : Finset (Fin n), G.IsNClique k S →
      (∀ S', G.IsNClique k S' → S' ≠ S → (S' ∩ S).card < delta n k) →
      ((∃ j, gridM n / 2 ≤ j ∧ j < gridM n ∧ ∃ α : Finset (Fin n), α.card = 3 ∧
          refine G k (selected ((j : ℝ) / gridM n) G k α) = S) ∨
        (∃ j ≤ gridM n / 2, ∃ α : Finset (Fin n), α.card = 3 ∧
          refine (G ⊔ Sampling.chunkGraph n (nBits n) j r) k
            (selected (1 / 2) (G ⊔ Sampling.chunkGraph n (nBits n) j r) k α) = S)) →
      S ∈ (alg (input G k, r)).map (vertexSet n)) ∧
    (0 < k → delta n k ≤ k → 2 * n * delta n k ≤ k ^ 2 →
      ((alg (input G k, r)).length : ℝ) ≤ n / k * (1 + 2 * n * delta n k / (k : ℝ) ^ 2)) := by
  classical
  have halg : alg (input G k, r) = cleanupL k (delta n k) (nonEdges n (adjBits G))
      (candHigh n k (gridM n) (nonEdges n (adjBits G)) ++
        candLow n k (nBits n) (gridM n) (adjBits G) r) := by
    simp only [alg, numV_input]
    rfl
  set C := candHigh n k (gridM n) (nonEdges n (adjBits G)) ++
    candLow n k (nBits n) (gridM n) (adjBits G) r with hC
  have hgood := good_candidates n k (nBits n) (gridM n) (nonEdges n (adjBits G)) (adjBits G) r
  have hmap := map_cleanupL (k := k) (Δ := delta n k) G hgood
  rw [halg]
  refine ⟨fun l hl ↦ ?_, fun S hS hother hcand ↦ ?_, fun hk hΔ h2 ↦ ?_⟩
  · have : vertexSet n l ∈ Pruning.cleanup G k (delta n k) (C.map (vertexSet n)) := by
      rw [← hmap]
      exact List.mem_map_of_mem hl
    exact Pruning.isNClique_of_mem_cleanup this
  · rw [hmap]
    refine Pruning.mem_cleanup ?_ hS hother
    have hM2 := two_le_gridM n
    rcases hcand with ⟨j, hj1, hj2, α, hα, rfl⟩ | ⟨j, hj, α, hα, rfl⟩
    · obtain ⟨αL, hnd, hl3, hset, hmem⟩ := exists_mem_triples hα
      refine List.mem_map.2 ⟨refineL k (nonEdges n (adjBits G))
        (selectedL n (gridM n) j k (nonEdges n (adjBits G)) (αL.map Fin.val)), ?_, ?_⟩
      · refine List.mem_append_left _ (List.mem_flatMap.2 ⟨j, ?_, List.mem_map.2 ⟨_, hmem, rfl⟩⟩)
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hj2, hj1⟩
      · rw [vertexSet_refineL (nonEdgesOf_nonEdges G) (good_selectedL _ _ _ _ _ _),
          vertexSet_selectedL (by omega) hj2 (nonEdgesOf_nonEdges G) hnd hl3, hset]
    · obtain ⟨αL, hnd, hl3, hset, hmem⟩ := exists_mem_triples hα
      set E' := nonEdgesAug n (nBits n) j (adjBits G) r
      refine List.mem_map.2 ⟨refineL k E' (selectedL n (gridM n) (gridM n / 2) k E'
        (αL.map Fin.val)), ?_, ?_⟩
      · refine List.mem_append_right _ (List.mem_flatMap.2 ⟨j, ?_, List.mem_map.2 ⟨_, hmem, rfl⟩⟩)
        simp only [List.mem_range]
        omega
      · rw [vertexSet_refineL (nonEdgesOf_nonEdgesAug G r) (good_selectedL _ _ _ _ _ _),
          vertexSet_selectedL (by omega) (by omega) (nonEdgesOf_nonEdgesAug G r) hnd hl3, hset,
          gridM_half]
  · have := Pruning.length_cleanup_le (G := G) (C := C.map (vertexSet n)) hk hΔ h2
    rw [← hmap, List.length_map] at this
    exact this

end BBKS24.Alg
