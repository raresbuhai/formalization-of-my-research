module

public import Background.RandomGraph

/-!
# The statistic of the algorithm, and recovery

The deterministic part of [BBKS24, §3–4]: the inner products of the algorithm, their split into
the planted set and the rest, and the recovery of the planted set from bounds on the random cut
(Lemmas 3.2, 3.5, 3.6 and 4.2–4.4, and the proofs of Lemma 3.7 and Theorem 4.1).

Let `χ = χ_q` be the `q`-biased character of an edge (`RandomGraph.chi`): `p₊ = √((1-q)/q)` for
an edge, `-p₋ = -√(q/(1-q))` for a non-edge. The algorithm, for every triple `α` of vertices,
forms the statistic `⟨Ḡ_α, Ḡ_j⟩ = ∑ᵢ ∏_{a ∈ α} χ(a ~ i) · χ(j ~ i)` for every vertex `j`
(`BBKS24.stat`), where `a ~ i` is adjacency *or equality* (`BBKS24.radj`): so on the planted
clique `S*` every factor is `p₊`. It keeps the vertices with statistic at least `k p₊⁴ / 2`
(`BBKS24.selected`), then those with at least `k - 1` neighbours among the kept ones
(`BBKS24.refine`).

For `α ⊆ S*` with `|α| = 3`:
* `j ∈ S*`: the statistic is `k p₊⁴` plus a sum over `i ∉ S*` of products of characters of the
  random cut (`BBKS24.stat_eq_of_mem`);
* `j ∉ S*`: it is `p₊³ ∑_{i ∈ S*} χ(j ~ i)`, a sum of characters of the random edges of `j`, plus
  the correlation of the column `H_α = (∏_{a∈α} χ(a ~ i))_{i ∉ S*}` with the vector
  `u_j = (χ(j ~ i))_{i ∉ S*}` that the adversary chooses (`BBKS24.stat_eq_of_not_mem`).

**Recovery** (`BBKS24.exists_refine_eq`): if the sums over the cut are at most `t₁`
(`j ∈ S*`) and `t₂` (`j ∉ S*`), and no `u` with entries at most `p₋` has correlation at least `τ`
with `s` columns `H_α`, then for suitable parameters some triple `α ⊆ S*` has refined set exactly
`S*`. The paper picks `α` at random and uses Markov's inequality; we average over all triples of
`S*` (the algorithm tries them all).

We take `q ≥ 1/2`; smaller `q` are reduced to `1/2` by adding random edges.
-/

@[expose] public section

open Finset RandomGraph

namespace BBKS24

/-! ### Characters -/

section Chars

variable {q : ℝ}

/-- `p₊ = √((1-q)/q)`, the character of an edge. -/
noncomputable def pplus (q : ℝ) : ℝ := √((1 - q) / q)

/-- `p₋ = √(q/(1-q))`: the character of a non-edge is `-p₋`. -/
noncomputable def pminus (q : ℝ) : ℝ := √(q / (1 - q))

theorem chi_of {b : Prop} (h : b) : chi q b = pplus q := by
  unfold chi pplus
  simp [h]

theorem chi_of_not {b : Prop} (h : ¬ b) : chi q b = -pminus q := by
  unfold chi pminus
  simp [h]

theorem chi_congr {b c : Prop} (h : b ↔ c) : chi q b = chi q c := by
  rw [propext h]

/-- `p₊ = √(1-q)/√q` and `p₋ = √q/√(1-q)`. -/
theorem pplus_eq (hq : 0 < q) : pplus q = √(1 - q) / √q := by
  rw [pplus, Real.sqrt_div' _ hq.le]

theorem pminus_eq (hq1 : q < 1) : pminus q = √q / √(1 - q) := by
  rw [pminus, Real.sqrt_div' _ (by linarith)]

theorem pplus_pos (hq : 0 < q) (hq1 : q < 1) : 0 < pplus q := by
  rw [pplus_eq hq]
  have : 0 < 1 - q := by linarith
  positivity

theorem pminus_pos (hq : 0 < q) (hq1 : q < 1) : 0 < pminus q := by
  rw [pminus_eq hq1]
  have : 0 < 1 - q := by linarith
  positivity

theorem pplus_mul_pminus (hq : 0 < q) (hq1 : q < 1) : pplus q * pminus q = 1 := by
  rw [pplus_eq hq, pminus_eq hq1]
  have h1 : 0 < √(1 - q) := Real.sqrt_pos.2 (by linarith)
  have h2 : 0 < √q := Real.sqrt_pos.2 hq
  field_simp

theorem pplus_le_one (hq : 1 / 2 ≤ q) (hq1 : q < 1) : pplus q ≤ 1 := by
  rw [pplus, Real.sqrt_le_one, div_le_one (by linarith)]
  linarith

theorem one_le_pminus (hq : 1 / 2 ≤ q) (hq1 : q < 1) : 1 ≤ pminus q := by
  rw [pminus, Real.one_le_sqrt, one_le_div (by linarith)]
  linarith

theorem abs_chi_le (hq : 1 / 2 ≤ q) (hq1 : q < 1) (b : Prop) : |chi q b| ≤ pminus q := by
  by_cases h : b
  · rw [chi_of h, abs_of_pos (pplus_pos (by linarith) hq1)]
    exact (pplus_le_one hq hq1).trans (one_le_pminus hq hq1)
  · rw [chi_of_not h, abs_neg, abs_of_pos (pminus_pos (by linarith) hq1)]

/-- **Degrees from characters.** If `d` of the `m` coins `b w`, `w ∈ T`, are heads, then
`∑ χ(b w) = d p₊ - (m - d) p₋`, so `d = q m + √(q(1-q)) ∑ χ(b w)`. -/
theorem card_filter_eq {ι : Type*} (hq : 0 < q) (hq1 : q < 1) (T : Finset ι) (b : ι → Prop)
    [DecidablePred b] :
    ((T.filter b).card : ℝ) = q * T.card + √(q * (1 - q)) * ∑ w ∈ T, chi q (b w) := by
  have hsum : ∑ w ∈ T, chi q (b w) =
      (T.filter b).card * pplus q - (T.card - (T.filter b).card) * pminus q := by
    rw [← sum_filter_add_sum_filter_not T b]
    rw [sum_congr rfl fun w hw ↦ chi_of (mem_filter.1 hw).2,
      sum_congr rfl fun w hw ↦ chi_of_not (mem_filter.1 hw).2, sum_const, sum_const,
      nsmul_eq_mul, nsmul_eq_mul]
    have := card_filter_add_card_filter_not (s := T) b
    have h' : ((T.filter fun w ↦ ¬ b w).card : ℝ) = T.card - (T.filter b).card := by
      rw [← this]
      push_cast
      ring
    rw [h']
    ring
  rw [hsum, pplus_eq hq, pminus_eq hq1, Real.sqrt_mul hq.le]
  have h1 : 0 < √(1 - q) := Real.sqrt_pos.2 (by linarith)
  have h2 : 0 < √q := Real.sqrt_pos.2 hq
  have hs1 := Real.sq_sqrt (show 0 ≤ 1 - q by linarith)
  have hs2 := Real.sq_sqrt hq.le
  field_simp
  nlinarith [hs1, hs2]

end Chars

/-! ### The statistic -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjacency or equality: the adjacency matrix with ones on the diagonal. -/
def radj (G : SimpleGraph V) (a i : V) : Prop := a = i ∨ G.Adj a i

/-- **The statistic** `⟨Ḡ_α, Ḡ_j⟩ = ∑ᵢ ∏_{a ∈ α} χ(a ~ i) χ(j ~ i)`. -/
noncomputable def stat (q : ℝ) (G : SimpleGraph V) (α : Finset V) (j : V) : ℝ :=
  ∑ i, (∏ a ∈ α, chi q (radj G a i)) * chi q (radj G j i)

open Classical in
/-- **The selected vertices** `S_α`: statistic at least `k p₊⁴ / 2`. -/
noncomputable def selected (q : ℝ) (G : SimpleGraph V) (k : ℕ) (α : Finset V) : Finset V :=
  univ.filter fun j ↦ k * pplus q ^ 4 / 2 ≤ stat q G α j

open Classical in
/-- **The refinement** of `T`: the vertices of `T` with at least `k - 1` neighbours in `T`. -/
noncomputable def refine (G : SimpleGraph V) (k : ℕ) (T : Finset V) : Finset V :=
  T.filter fun j ↦ k - 1 ≤ (T.filter (G.Adj j)).card

/-- The correlation, over the vertices outside `S`, of the column of the triple `α` with the
character of the edges to `j ∈ S`: a function of the cut `x`. -/
noncomputable def inCorr (q : ℝ) (S α : Finset V) (j : {w // w ∈ S})
    (x : {v // v ∉ S} → {w // w ∈ S} → Prop) : ℝ :=
  ∑ i, blockChar S q α (x i) * chi q (x i j)

/-- The planted graph: `G` has a clique on `S`, and its edges between `S` and the other vertices
are those of `R`. -/
structure Planted (G R : SimpleGraph V) (S : Finset V) : Prop where
  clique : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b
  onCut : ∀ a ∈ S, ∀ v ∉ S, (G.Adj a v ↔ R.Adj a v)

variable {q : ℝ} {G R : SimpleGraph V} {S : Finset V}

omit [Fintype V] [DecidableEq V] in
theorem Planted.radj_of_mem (hP : Planted G R S) {a i : V} (ha : a ∈ S) (hi : i ∈ S) :
    radj G a i := by
  by_cases h : a = i
  · exact Or.inl h
  · exact Or.inr (hP.clique a ha i hi h)

omit [Fintype V] [DecidableEq V] in
theorem Planted.radj_iff_cut (hP : Planted G R S) {a i : V} (ha : a ∈ S) (hi : i ∉ S) :
    radj G a i ↔ cut S R ⟨i, hi⟩ ⟨a, ha⟩ := by
  have hne : a ≠ i := fun h ↦ hi (h ▸ ha)
  simp only [radj, hne, false_or, cut]
  exact hP.onCut a ha i hi

omit [Fintype V] [DecidableEq V] in
theorem Planted.radj_iff_cut' (hP : Planted G R S) {j i : V} (hj : j ∉ S) (hi : i ∈ S) :
    radj G j i ↔ cut S R ⟨j, hj⟩ ⟨i, hi⟩ := by
  have hne : j ≠ i := fun h ↦ hj (h ▸ hi)
  simp only [radj, hne, false_or, cut]
  exact ⟨fun h ↦ (hP.onCut i hi j hj).1 h.symm, fun h ↦ ((hP.onCut i hi j hj).2 h).symm⟩

omit [Fintype V] in
theorem Planted.prod_chi_eq (hP : Planted G R S) {α : Finset V} (hα : α ⊆ S) {i : V}
    (hi : i ∉ S) :
    ∏ a ∈ α, chi q (radj G a i) = blockChar S q α (cut S R ⟨i, hi⟩) := by
  rw [blockChar, ← prod_subtype_of_mem (fun a ↦ chi q (radj G a i)) hα]
  exact prod_congr rfl fun a _ ↦ chi_congr (hP.radj_iff_cut a.2 hi)

/-- Split a sum over the vertices into the planted set and the rest. -/
theorem sum_split (S : Finset V) (f : V → ℝ) :
    ∑ i, f i = ∑ i : {w // w ∈ S}, f i + ∑ i : {v // v ∉ S}, f i := by
  rw [← sum_add_sum_compl S f, sum_coe_sort S f]
  congr 1
  exact sum_subtype _ (fun x ↦ mem_compl) f

/-- **The statistic for `j ∈ S`**: `k p₊⁴` plus the correlation over the cut. -/
theorem stat_eq_of_mem (hP : Planted G R S) {α : Finset V} (hα : α ⊆ S) (h3 : α.card = 3)
    {j : V} (hj : j ∈ S) :
    stat q G α j = S.card * pplus q ^ 4 + inCorr q S α ⟨j, hj⟩ (cut S R) := by
  rw [stat, sum_split S]
  congr 1
  · have : ∀ i : {w // w ∈ S}, (∏ a ∈ α, chi q (radj G a i)) * chi q (radj G j i) =
        pplus q ^ 4 := by
      intro i
      rw [prod_congr rfl fun a ha ↦ chi_of (hP.radj_of_mem (hα ha) i.2), prod_const, h3,
        chi_of (hP.radj_of_mem hj i.2)]
      ring
    rw [sum_congr rfl fun i _ ↦ this i, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
  · refine sum_congr rfl fun i _ ↦ ?_
    rw [hP.prod_chi_eq hα i.2, chi_congr (hP.radj_iff_cut hj i.2)]

/-- **The statistic for `j ∉ S`**: `p₊³` times the characters of the edges between `j` and `S`,
plus the correlation of the column `H_α` with `u_j = χ(j ~ ·)`. -/
theorem stat_eq_of_not_mem (hP : Planted G R S) {α : Finset V} (hα : α ⊆ S) (h3 : α.card = 3)
    {j : V} (hj : j ∉ S) :
    stat q G α j = pplus q ^ 3 * ∑ w, chi q (cut S R ⟨j, hj⟩ w) +
      ∑ i : {v // v ∉ S}, blockChar S q α (cut S R i) * chi q (radj G j i) := by
  rw [stat, sum_split S, mul_sum]
  congr 1
  · refine sum_congr rfl fun i _ ↦ ?_
    rw [prod_congr rfl fun a ha ↦ chi_of (hP.radj_of_mem (hα ha) i.2), prod_const, h3,
      chi_congr (hP.radj_iff_cut' hj i.2)]
  · exact sum_congr rfl fun i _ ↦ by rw [hP.prod_chi_eq hα i.2]

omit [Fintype V] [DecidableEq V] in
/-- The degree of `j ∉ S` into `S`: `q |S| + √(q(1-q)) ∑_{w ∈ S} χ(j ~ w)`. -/
theorem card_filter_adj_eq (hP : Planted G R S) (hq : 0 < q) (hq1 : q < 1) {j : V} (hj : j ∉ S)
    [DecidableRel G.Adj] :
    ((S.filter (G.Adj j)).card : ℝ) =
      q * S.card + √(q * (1 - q)) * ∑ w, chi q (cut S R ⟨j, hj⟩ w) := by
  rw [card_filter_eq hq hq1 S (G.Adj j)]
  congr 2
  rw [← sum_coe_sort S]
  refine sum_congr rfl fun w _ ↦ chi_congr ?_
  have := hP.radj_iff_cut' hj w.2
  simp only [radj, show j ≠ (w : V) from fun h ↦ hj (h ▸ w.2), false_or] at this
  exact this

/-! ### Recovery -/

/-- **Recovery** [BBKS24, Lemmas 3.2, 3.5, 3.6, 4.2–4.4]. Let `G` be planted on `S`, `|S| = k`,
with the edges between `S` and the rest from `R`, and `1/2 ≤ q < 1`. Suppose that

* (all good) for every triple `α ⊆ S` and `j ∈ S`, the correlation over the cut is at most `t₁`;
* (degrees) for every `j ∉ S`, `|∑_{w ∈ S} χ(j ~ w)| ≤ t₂`;
* (few bad) no vector with entries at most `p₋` has correlation at least `τ` with `s` columns
  `H_α`;

and that `t₁ ≤ k p₊⁴/2`, `τ ≤ k p₊⁴/2 - p₊³ t₂` and
`q k + √(q(1-q)) t₂ + (n - k) s / C(k, 3) < k - 1`. Then some triple `α ⊆ S` has
`refine G k (selected q G k α) = S`. -/
theorem exists_refine_eq (hP : Planted G R S) (hq : 1 / 2 ≤ q) (hq1 : q < 1) {k : ℕ}
    (hk : S.card = k) (hk3 : 3 ≤ k) {t₁ t₂ τ : ℝ} {s : ℕ}
    (hE1 : ∀ α ⊆ S, α.card = 3 → ∀ j (hj : j ∈ S), |inCorr q S α ⟨j, hj⟩ (cut S R)| ≤ t₁)
    (hE2 : ∀ j (hj : j ∉ S), |∑ w, chi q (cut S R ⟨j, hj⟩ w)| ≤ t₂)
    (hE3 : ∀ u : {v // v ∉ S} → ℝ, (∀ i, |u i| ≤ pminus q) →
      ((S.powersetCard 3).filter fun α ↦
        τ ≤ ∑ i, blockChar S q α (cut S R i) * u i).card < s)
    (h1 : t₁ ≤ k * pplus q ^ 4 / 2) (h2 : τ ≤ k * pplus q ^ 4 / 2 - pplus q ^ 3 * t₂)
    (h3 : q * k + √(q * (1 - q)) * t₂ + (Fintype.card V - k) * s / k.choose 3 < k - 1) :
    ∃ α ∈ S.powersetCard 3, refine G k (selected q G k α) = S := by
  classical
  have hq0 : 0 < q := by linarith
  have hp3 : 0 ≤ pplus q ^ 3 := pow_nonneg (pplus_pos hq0 hq1).le 3
  set T₃ := S.powersetCard 3 with hT₃
  have hT₃card : T₃.card = k.choose 3 := by rw [hT₃, card_powersetCard, hk]
  have hT₃pos : 0 < T₃.card := by
    rw [hT₃card]
    exact Nat.choose_pos hk3
  -- (i) All good: `S ⊆ S_α`.
  have hin : ∀ α ∈ T₃, S ⊆ selected q G k α := by
    intro α hα j hj
    obtain ⟨hαS, hα3⟩ := mem_powersetCard.1 hα
    simp only [selected, mem_filter, mem_univ, true_and]
    rw [stat_eq_of_mem hP hαS hα3 hj, hk]
    have := neg_abs_le (inCorr q S α ⟨j, hj⟩ (cut S R))
    have := hE1 α hαS hα3 j hj
    linarith
  -- (ii) Few bad: each `j ∉ S` is selected by fewer than `s` triples.
  have hbad : ∀ j ∉ S, (T₃.filter fun α ↦ j ∈ selected q G k α).card < s := by
    intro j hj
    refine lt_of_le_of_lt (card_le_card fun α hα ↦ ?_)
      (hE3 (fun i ↦ chi q (radj G j i)) fun i ↦ abs_chi_le hq hq1 _)
    obtain ⟨hαT, hsel⟩ := mem_filter.1 hα
    obtain ⟨hαS, hα3⟩ := mem_powersetCard.1 hαT
    refine mem_filter.2 ⟨hαT, ?_⟩
    simp only [selected, mem_filter, mem_univ, true_and] at hsel
    rw [stat_eq_of_not_mem hP hαS hα3 hj] at hsel
    have := le_abs_self (∑ w, chi q (cut S R ⟨j, hj⟩ w))
    have := mul_le_mul_of_nonneg_left (hE2 j hj) hp3
    nlinarith
  -- (iii) Averaging over the triples of `S`.
  have hsum : ∑ α ∈ T₃, ((selected q G k α \ S).card : ℝ) ≤
      (Fintype.card V - k) * s := by
    have : ∀ α ∈ T₃, ((selected q G k α \ S).card : ℝ) =
        ∑ j ∈ Sᶜ, if j ∈ selected q G k α then 1 else 0 := by
      intro α _
      rw [sum_boole]
      congr 1
      congr 1
      ext j
      simp [and_comm]
    rw [sum_congr rfl this, sum_comm]
    calc ∑ j ∈ Sᶜ, ∑ α ∈ T₃, (if j ∈ selected q G k α then (1 : ℝ) else 0)
        = ∑ j ∈ Sᶜ, ((T₃.filter fun α ↦ j ∈ selected q G k α).card : ℝ) :=
          sum_congr rfl fun j _ ↦ by rw [sum_boole]
      _ ≤ ∑ _j ∈ Sᶜ, (s : ℝ) := sum_le_sum fun j hj ↦ by
          exact_mod_cast (hbad j (mem_compl.1 hj)).le
      _ = (Fintype.card V - k) * s := by
          rw [sum_const, nsmul_eq_mul, card_compl, hk]
          have : k ≤ Fintype.card V := hk ▸ card_le_univ S
          push_cast [this]
          ring
  obtain ⟨α, hα, hαle⟩ : ∃ α ∈ T₃,
      ((selected q G k α \ S).card : ℝ) ≤ (Fintype.card V - k) * s / k.choose 3 := by
    refine exists_le_of_sum_le (card_pos.1 hT₃pos) (hsum.trans_eq ?_)
    rw [sum_const, nsmul_eq_mul, hT₃card]
    have : (0 : ℝ) < k.choose 3 := by exact_mod_cast Nat.choose_pos hk3
    field_simp
  refine ⟨α, hα, ?_⟩
  -- (iv) The refinement keeps exactly `S`.
  have hS := hin α hα
  set T := selected q G k α
  ext j
  simp only [refine, mem_filter]
  constructor
  · rintro ⟨hjT, hdeg⟩
    by_contra hjS
    -- `j ∉ S` has fewer than `k - 1` neighbours in `T`.
    have hsub : T.filter (G.Adj j) ⊆ S.filter (G.Adj j) ∪ (T \ S) := by
      intro w hw
      obtain ⟨hwT, hadj⟩ := mem_filter.1 hw
      by_cases hwS : w ∈ S
      · exact mem_union_left _ (mem_filter.2 ⟨hwS, hadj⟩)
      · exact mem_union_right _ (mem_sdiff.2 ⟨hwT, hwS⟩)
    have hcard : ((T.filter (G.Adj j)).card : ℝ) ≤ (S.filter (G.Adj j)).card + (T \ S).card := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    have hdegS := card_filter_adj_eq hP hq0 hq1 hjS (G := G)
    have hE := hE2 j hjS
    have hsq : 0 ≤ √(q * (1 - q)) := Real.sqrt_nonneg _
    have := le_abs_self (∑ w, chi q (cut S R ⟨j, hjS⟩ w))
    have := mul_le_mul_of_nonneg_left hE hsq
    have hdegR : ((k - 1 : ℕ) : ℝ) ≤ (T.filter (G.Adj j)).card := by exact_mod_cast hdeg
    have hk1 : ((k - 1 : ℕ) : ℝ) = k - 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hk1] at hdegR
    rw [hk] at hdegS
    nlinarith
  · intro hjS
    refine ⟨hS hjS, ?_⟩
    have : S.erase j ⊆ T.filter (G.Adj j) := fun w hw ↦ by
      obtain ⟨hwj, hwS⟩ := mem_erase.1 hw
      exact mem_filter.2 ⟨hS hwS, hP.clique j hjS w hwS (Ne.symm hwj)⟩
    calc k - 1 = (S.erase j).card := by rw [card_erase_of_mem hjS, hk]
      _ ≤ (T.filter (G.Adj j)).card := card_le_card this

end BBKS24
