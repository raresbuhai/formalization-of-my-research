module

public import BGHKLMM26.IntGap.Instance
public import BGHKLMM26.Hardness.Main

/-!
# The SDP value of the dense graph

The reduction of Theorem 1.2 numbers the long-code vertex `(v, x)`, `x ∈ {0,1}^R`, as
`v 2^R + idx x` (`BGHKLMM26.Hard.vtx`). For the instance `kvInst k z` (`R = 2^k`),
`BGHKLMM26.IntGap.lcVert k a` reads the number `a` back as the class of `a / 2^R` and the point
of `a % 2^R`, with its coordinates indexed by the labels, and `BGHKLMM26.IntGap.Knum` is the
long-code kernel `BGHKLMM26.IntGap.lcK` on numbers.

**The dense value** (`BGHKLMM26.IntGap.avgExact_Knum_le`): on an edge between `(v₁, π₁ x)` and
`(v₂, π₂ y)` of the KKMO graph, `y` `ρ`-correlated with `x`, the expected product of the signs of
coordinates `j₁, j₂` is `ρ` when `π₁ j₁ = π₂ j₂` and `0` otherwise, so the kernel averages to
`ρ (1/Δ) Σᵢ (1/N) Σ_j ⟨T_{v₁, j}, T_{v₂, m(j)}⟩^{sᵢ}` with `m` the matching through the left
vertex; each inner product is at least `1 - 4z/N` (`BGHKLMM26.IntGap.kv_close`), and
`(1 - 4z/N)^s ≥ 1 - 4zs/N`. With `ρ ≤ 0` this bounds the average from above.
-/

@[expose] public section

namespace BGHKLMM26.IntGap

open UniqueGames

open scoped RealInnerProductSpace
open Hard OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.GaussianBellman

variable (k : ℕ)

/-- The long-code vertex numbered `a`, for `R = 2^k` labels. -/
noncomputable def lcVert (a : ℕ) : Cls k × (Lab k → Bool) :=
  (clsOf k (a / 2 ^ 2 ^ k), fun t ↦ (a % 2 ^ 2 ^ k).testBit (labIdx k t))

/-- The long-code kernel on vertex numbers. -/
noncomputable def Knum (T Δ : ℕ) (e : ℕ × ℕ) : ℝ := lcK (kvTup k) T Δ (lcVert k e.1) (lcVert k e.2)

variable {k}

/-- Bit `i` of the value of a bit string is its entry `i`. -/
theorem dense_testBit_bitsVal (l : List Bool) (i : ℕ) : (bitsVal l).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp [bitsVal]
  | cons b l ih =>
    cases i with
    | zero => cases b <;> simp [bitsVal]
    | succ i =>
      have h : bitsVal (b :: l) / 2 = bitsVal l := by
        simp only [bitsVal]; split <;> omega
      rw [Nat.testBit_succ, h, ih]
      rfl

/-- Bit `i` of the index of a point of the cube is its coordinate `i`. -/
theorem dense_testBit_cubeIdx {R : ℕ} (x : Cube (Fin R)) (i : Fin R) :
    (cubeIdx x).testBit i = x i := by
  rw [cubeIdx, dense_testBit_bitsVal, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

/-- `BGHKLMM26.IntGap.lcVert_vtx` without the bound on `v`. -/
theorem dense_lcVert_vtx (v : ℕ) (x : Cube (Fin (2 ^ k))) :
    lcVert k (vtx v x) = (clsOf k v, fun t ↦ x (labIdx k t)) := by
  obtain ⟨h1, h2⟩ := vtx_eq_iff.1 (rfl : vtx v x = vtx v x)
  simp only [lcVert, ← h1, ← h2, dense_testBit_cubeIdx]

theorem lcVert_vtx {v : ℕ} (_hv : v < Fintype.card (Cls k)) (x : Cube (Fin (2 ^ k))) :
    lcVert k (vtx v x) = (clsOf k v, fun t ↦ x (labIdx k t)) :=
  dense_lcVert_vtx v x

/-- The long-code kernel is symmetric. -/
theorem dense_lcK_comm {V L I : Type} [Fintype V] [Fintype L] [AddCommGroup L] [Fintype I]
    [DecidableEq L] (S : SymTuples V L I) (T Δ : ℕ) (a b : V × (L → Bool)) :
    lcK S T Δ a b = lcK S T Δ b a := by
  unfold lcK
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun m _ ↦ ?_
  rw [real_inner_comm]
  ring

theorem Knum_comm (T Δ : ℕ) (a b : ℕ) : Knum k T Δ (a, b) = Knum k T Δ (b, a) :=
  dense_lcK_comm _ _ _ _ _

/-- The correlated average of a constant. -/
theorem dense_corrAverage_const (t c : ℝ) (n : ℕ) : corrAverage t n (fun _ _ ↦ c) = c := by
  have := corrAverage_fst t n (fun _ ↦ c)
  rwa [Fintype.expect_const] at this

/-- The average of an affine function over a nonempty list. -/
theorem dense_list_avg_affine {α : Type*} {l : List α} (hl : l ≠ []) (a b : ℝ) (f : α → ℝ) :
    (l.map fun x ↦ a + b * f x).sum / l.length = a + b * ((l.map f).sum / l.length) := by
  have h : (l.length : ℝ) ≠ 0 := by exact_mod_cast (List.length_pos_iff.2 hl).ne'
  rw [List.sum_map_add, List.sum_map_mul_left, List.map_const', List.sum_replicate, nsmul_eq_mul]
  field_simp

theorem dense_pairAvg_affine {P : Prm} (a b : ℝ) (φ : ℕ × ℕ → ℝ) (c₁ c₂ : UGConstraint) :
    pairAvg (P := P) (fun e ↦ a + b * φ e) c₁ c₂ = a + b * pairAvg (P := P) φ c₁ c₂ := by
  unfold pairAvg
  rw [corrAverage_add, dense_corrAverage_const, corrAverage_const_mul]

/-- **The average over the exact law is affine.** -/
theorem avgExact_affine {P : Prm} {G : UGInstance} (_hq : P.q ≤ 2 ^ P.b) (hcs : G.2.2.2 ≠ [])
    (α β : ℝ) (φ : ℕ × ℕ → ℝ) :
    avgExact (P := P) (G := G) (fun e ↦ α + β * φ e) = α + β * avgExact (P := P) (G := G) φ := by
  unfold avgExact
  simp only [dense_pairAvg_affine]
  have h1 : ∀ c₁ ∈ G.2.2.2, ((nbrs G.2.2.2 c₁.1.1).map fun c₂ ↦
      α + β * pairAvg (P := P) φ c₁ c₂).sum / (nbrs G.2.2.2 c₁.1.1).length =
        α + β * (((nbrs G.2.2.2 c₁.1.1).map fun c₂ ↦ pairAvg (P := P) φ c₁ c₂).sum /
          (nbrs G.2.2.2 c₁.1.1).length) := fun c₁ hc₁ ↦
    dense_list_avg_affine (List.ne_nil_of_mem (mem_nbrs_self hc₁)) α β _
  rw [List.map_congr_left h1, dense_list_avg_affine hcs]

/-- **The decoded law** averages within `B / 2^Δ` of the exact law, for `|φ| ≤ B`. -/
theorem mean_dec_ge {P : Prm} {G : UGInstance} (hq : P.q ≤ 2 ^ P.b) (hG : GoodI P.R G)
    (hok : P.ok G = true) {φ : ℕ × ℕ → ℝ} {B : ℝ} (hB : ∀ e, |φ e| ≤ B) :
    avgExact (P := P) (G := G) φ - B / 2 ^ P.Δ ≤
      mean (fun ω ↦ φ ((dec hG hok ω).1.1, (dec hG hok ω).2.1)) := by
  have hcs : G.2.2.2 ≠ [] := List.length_pos_iff.1 (ok_iff.1 hok).2.1
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (0, 0))
  have h1 := (abs_le.1 (abs_avgDec_sub_le hq hcs hB)).1
  have h2 := mul_le_mul_of_nonneg_left ((tv_le hG hok).trans (tv_le_two_pow hG hok)) hB0
  have hmean : mean (fun ω ↦ φ ((dec hG hok ω).1.1, (dec hG hok ω).2.1)) =
      (∑ ω : Fin (P.blockLen G) → Bool, φ (decE P G ω)) / 2 ^ P.blockLen G := by
    rw [mean, card_block]
    rfl
  have h3 : 2 * (G.2.2.2.length : ℝ) * B / 2 ^ P.tBits G =
      B * (2 * (G.2.2.2.length : ℝ) * 1 / 2 ^ P.tBits G) := by ring
  have h4 : B * (1 / 2 ^ P.Δ) = B / 2 ^ P.Δ := by ring
  rw [hmean]
  linarith

/-! ### The dense value -/

/-- The correlation of two sign coordinates of `ρ`-correlated points. -/
theorem dense_corrAverage_pm (t : ℝ) (n : ℕ) (i j : Fin n) :
    corrAverage t n (fun x y ↦ pm (x i) * pm (y j)) = if i = j then t else 0 := by
  have hw (i : Fin n) (x : BitCube n) :
      OAI.MaxCutGames.Foundations.Hastad.walsh (fun l ↦ decide (l = i)) x = pm (x i) := by
    rw [OAI.MaxCutGames.Foundations.Hastad.walsh,
      Finset.prod_eq_single i (fun l _ hl ↦ by simp [hl, bitSign]) (by simp)]
    simp [pm, bitSign]
  have := OAI.OptimalMaxCut.MISProof.corrAverage_walsh t n (fun l ↦ decide (l = i))
    (fun l ↦ decide (l = j))
  simp only [hw] at this
  rw [this]
  by_cases h : i = j
  · subst h
    simp [OAI.OptimalMaxCut.Analytic.degree, Finset.filter_eq']
  · rw [ite_eq_right h, ite_eq_right]
    intro hf
    exact h (by simpa using congrFun hf i)

theorem dense_permCube_apply {R : ℕ} {π : List ℕ} {j : Fin R} (h : π.getD j 0 < R)
    (x : Cube (Fin R)) : permCube π x j = x ⟨π.getD j 0, h⟩ := dite_eq_left h

/-- The correlation of two sign coordinates read through tables. -/
theorem dense_corrAverage_pm_perm (t : ℝ) {n : ℕ} {π₁ π₂ : List ℕ}
    (h₁ : ∀ j : Fin n, π₁.getD j 0 < n) (h₂ : ∀ j : Fin n, π₂.getD j 0 < n) (j₁ j₂ : Fin n) :
    corrAverage t n (fun x y ↦ pm (permCube π₁ x j₁) * pm (permCube π₂ y j₂)) =
      if π₁.getD j₁ 0 = π₂.getD j₂ 0 then t else 0 := by
  simp only [dense_permCube_apply (h₁ j₁), dense_permCube_apply (h₂ j₂), dense_corrAverage_pm,
    Fin.mk.injEq]

theorem dense_corrAverage_div (t c : ℝ) (n : ℕ) (F : BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y ↦ F x y / c) = corrAverage t n F / c := by
  simpa only [div_eq_mul_inv] using corrAverage_mul_const t c⁻¹ n F

/-- The correlated average of the long-code kernel. -/
theorem dense_corrAverage_lcK {V L I : Type} [Fintype V] [Fintype L] [AddCommGroup L] [Fintype I]
    [DecidableEq L] (S : SymTuples V L I) (T Δ : ℕ) (t : ℝ) (n : ℕ) (u v : V)
    (f g : BitCube n → L → Bool) :
    corrAverage t n (fun x y ↦ lcK S T Δ (u, f x) (v, g y)) =
      (∑ i ∈ Finset.range Δ, (∑ s, ∑ l, corrAverage t n (fun x y ↦ pm (f x s) * pm (g y l)) *
        ⟪S.vec u s, S.vec v l⟫ ^ tExp T i) / Fintype.card L) / Δ := by
  simp only [lcK, dense_corrAverage_div, OAI.OptimalMaxCut.MISProof.corrAverage_sum,
    corrAverage_mul_const]

/-- An entry of a table of length `N` with entries below `N`. -/
theorem dense_getD_lt {N : ℕ} {π : List ℕ} (hlen : π.length = N) (hlt : ∀ a ∈ π, a < N)
    (j : Fin N) : π.getD j 0 < N := by
  have hj : (j : ℕ) < π.length := hlen ▸ j.2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact hlt _ (List.getElem_mem hj)

/-- A table of length `N` without repetitions and with entries below `N` takes every value. -/
theorem dense_exists_getD_eq {N : ℕ} {π : List ℕ} (hlen : π.length = N) (hnd : π.Nodup)
    (hlt : ∀ a ∈ π, a < N) {a : ℕ} (ha : a < N) : ∃ j : Fin N, π.getD j 0 = a := by
  classical
  have hsub : π.toFinset ⊆ Finset.range N := fun b hb ↦
    Finset.mem_range.2 (hlt b (List.mem_toFinset.1 hb))
  have heq : π.toFinset = Finset.range N := Finset.eq_of_subset_of_card_le hsub
    (by rw [List.toFinset_card_of_nodup hnd, Finset.card_range, hlen])
  have hmem : a ∈ π := List.mem_toFinset.1 (heq ▸ Finset.mem_range.2 ha)
  obtain ⟨j, hj, hja⟩ := List.mem_iff_getElem.1 hmem
  refine ⟨⟨j, hlen ▸ hj⟩, ?_⟩
  change π.getD j 0 = a
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, hja]

theorem dense_labOf_labIdx (s : Lab k) : labOf k (labIdx k s) = s := by
  rw [labOf, dite_eq_left (labIdx k s).2]
  simp

/-- **Bernoulli's inequality** for `u ≥ max(0, 1 - a)`: `uⁿ ≥ 1 - n a` for `n ≥ 1`. -/
theorem dense_one_sub_mul_le_pow {u a : ℝ} (hu : 0 ≤ u) (hua : 1 - a ≤ u) {n : ℕ}
    (hn : 1 ≤ n) : 1 - n * a ≤ u ^ n := by
  rcases le_or_gt a 1 with h | h
  · have h1 : (1 - a) ^ n ≤ u ^ n := pow_le_pow_left₀ (by linarith) hua n
    have h2 := one_add_mul_le_pow (a := -a) (by linarith) n
    have h3 : 1 + (n : ℝ) * -a = 1 - n * a := by ring
    rw [h3, ← sub_eq_add_neg] at h2
    linarith
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : 0 ≤ u ^ n := pow_nonneg hu n
    nlinarith

theorem dense_one_le_tExp (T i : ℕ) : 1 ≤ tExp T i := by
  unfold tExp
  have := Nat.one_le_pow ((i + 1) * T) 4 (by norm_num)
  omega

theorem dense_tExp_le {T i Δ : ℕ} (hi : i < Δ) : tExp T i ≤ tExp T Δ := by
  unfold tExp
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega)))

/-- An average of values at most `C` is at most `C`. -/
theorem dense_sum_div_card_le {ι : Type*} {s : Finset ι} {n : ℕ} (hn : s.card = n) (hpos : 0 < n)
    {f : ι → ℝ} {C : ℝ} (h : ∀ i ∈ s, f i ≤ C) : (∑ i ∈ s, f i) / n ≤ C := by
  rw [div_le_iff₀ (by exact_mod_cast hpos)]
  have := Finset.sum_le_card_nsmul s f C h
  rw [hn, nsmul_eq_mul] at this
  linarith

/-- An average over a nonempty list of values at most `C` is at most `C`. -/
theorem dense_list_avg_le {α : Type*} {l : List α} (hl : l ≠ []) {f : α → ℝ} {C : ℝ}
    (h : ∀ a ∈ l, f a ≤ C) : (l.map f).sum / l.length ≤ C := by
  have hpos : (0 : ℝ) < l.length := by exact_mod_cast List.length_pos_iff.2 hl
  rw [div_le_iff₀ hpos]
  have := List.sum_le_length_nsmul (l.map f) C (by simpa using h)
  rw [List.length_map, nsmul_eq_mul] at this
  linarith

/-- The exact law averages to at most `C` when every pair of constraints at one left vertex
does. -/
theorem dense_avgExact_le {P : Prm} {G : UGInstance} (hcs : G.2.2.2 ≠ []) {φ : ℕ × ℕ → ℝ} {C : ℝ}
    (h : ∀ c₁ ∈ G.2.2.2, ∀ c₂ ∈ G.2.2.2, c₂.1.1 = c₁.1.1 → pairAvg (P := P) φ c₁ c₂ ≤ C) :
    avgExact (P := P) (G := G) φ ≤ C := by
  unfold avgExact
  refine dense_list_avg_le hcs fun c₁ hc₁ ↦
    dense_list_avg_le (List.ne_nil_of_mem (mem_nbrs_self hc₁)) fun c₂ hc₂ ↦ ?_
  obtain ⟨hc₂', he⟩ := List.mem_filter.1 hc₂
  exact h c₁ hc₁ c₂ hc₂' (by simpa using he)

/-- **The dense value on one pair of constraints** at one left vertex. -/
theorem dense_pairAvg_Knum_le {z T Δ : ℕ} {P : Prm} (hz : 2 * z < 2 ^ k) (hΔ : 1 ≤ Δ)
    (hR : P.R = 2 ^ k) (hρ : P.rho ≤ 0) {c₁ c₂ : UGConstraint} (hc₁ : c₁ ∈ (kvInst k z).2.2.2)
    (hc₂ : c₂ ∈ (kvInst k z).2.2.2) (h12 : c₁.1.1 = c₂.1.1) :
    pairAvg (P := P) (Knum k T Δ) c₁ c₂ ≤ P.rho * (1 - 4 * z / 2 ^ k * tExp T Δ) := by
  obtain ⟨R, b, q, D, Δ'⟩ := P
  change R = 2 ^ k at hR
  subst hR
  have hπ₁ := kv_table_perm hc₁
  have hπ₂ := kv_table_perm hc₂
  have h₁ : ∀ j : Fin (2 ^ k), c₁.2.getD j 0 < 2 ^ k := dense_getD_lt hπ₁.1 hπ₁.2.2
  have h₂ : ∀ j : Fin (2 ^ k), c₂.2.getD j 0 < 2 ^ k := dense_getD_lt hπ₂.1 hπ₂.2.2
  simp only [pairAvg, Knum, dense_lcVert_vtx]
  rw [dense_corrAverage_lcK]
  simp only [dense_corrAverage_pm_perm _ h₁ h₂]
  generalize Prm.rho _ = ρ at hρ ⊢
  have ha : 0 ≤ 4 * (z : ℝ) / 2 ^ k := by positivity
  refine dense_sum_div_card_le (Finset.card_range Δ) hΔ fun i hi ↦
    dense_sum_div_card_le Finset.card_univ Fintype.card_pos fun s _ ↦ ?_
  have hi' : i < Δ := Finset.mem_range.1 hi
  set W : Lab k → ℝ := fun l ↦
    ⟪(kvTup k).vec (clsOf k c₁.1.2) s, (kvTup k).vec (clsOf k c₂.1.2) l⟫ ^ tExp T i
  set p : Lab k → Prop := fun l ↦ c₁.2.getD (labIdx k s) 0 = c₂.2.getD (labIdx k l) 0
  have hsplit : ∑ l, (if p l then ρ else 0) * W l = ρ * ∑ l, (if p l then 1 else 0) * W l := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    split_ifs <;> ring
  change ∑ l, (if p l then ρ else 0) * W l ≤ _
  rw [hsplit]
  refine mul_le_mul_of_nonpos_left ?_ hρ
  -- the right label matched with `s` through the left label
  obtain ⟨j₂, hj₂⟩ := dense_exists_getD_eq hπ₂.1 hπ₂.2.1 hπ₂.2.2 (h₁ (labIdx k s))
  have hl₀ : labIdx k ((labIdx k).symm j₂) = j₂ := Equiv.apply_symm_apply _ _
  have hmatch : p ((labIdx k).symm j₂) := by
    change c₁.2.getD (labIdx k s) 0 = c₂.2.getD (labIdx k ((labIdx k).symm j₂)) 0
    rw [hl₀, hj₂]
  have hclose := kv_close (by omega) hc₁ hc₂ h12 (labIdx k s).2
    (labIdx k ((labIdx k).symm j₂)).2 hmatch
  rw [dense_labOf_labIdx, dense_labOf_labIdx] at hclose
  have hW0 : ∀ l, 0 ≤ W l := fun l ↦ pow_nonneg ((kvTup k).nonneg _ _ _ _) _
  have hsum : W ((labIdx k).symm j₂) ≤ ∑ l, (if p l then (1 : ℝ) else 0) * W l := by
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun l ↦
      (if p l then (1 : ℝ) else 0) * W l) (fun l _ ↦ mul_nonneg (by split_ifs <;> norm_num)
        (hW0 l)) (Finset.mem_univ ((labIdx k).symm j₂)))
    simp only [ite_eq_left hmatch, one_mul]
  have hbern := dense_one_sub_mul_le_pow ((kvTup k).nonneg _ _ _ _) hclose
    (dense_one_le_tExp T i)
  have hle : (tExp T i : ℝ) ≤ tExp T Δ := by exact_mod_cast dense_tExp_le hi'
  have := mul_le_mul_of_nonneg_left hle ha
  change 1 - _ * _ ≤ W _ at hbern
  linarith

/-- **The dense value**: the kernel averages to at most `ρ (1 - 4 z s / 2^k)` over the KKMO
graph of `kvInst k z`, `s = tExp T Δ` the largest exponent, when `ρ ≤ 0`. -/
theorem avgExact_Knum_le {z T Δ : ℕ} {P : Prm} (_hk : 1 ≤ k) (hz : 2 * z < 2 ^ k) (hΔ : 1 ≤ Δ)
    (hR : P.R = 2 ^ k) (_hq : P.q ≤ 2 ^ P.b) (hρ : P.rho ≤ 0) :
    avgExact (P := P) (G := kvInst k z) (Knum k T Δ) ≤
      P.rho * (1 - 4 * z / 2 ^ k * tExp T Δ) := by
  refine dense_avgExact_le (kvInst_ne (by omega)) fun c₁ hc₁ c₂ hc₂ h21 ↦ ?_
  exact dense_pairAvg_Knum_le hz hΔ hR hρ hc₁ hc₂ h21.symm

end BGHKLMM26.IntGap
