module

public import BHSV25.Alg.ExpanderAccount
public import BHSV25.Alg.Partition
public import BHSV25.Alg.ClusterPolyTime

/-!
# Coloring one-sided expanders with a given model

[BHSV25, Theorems 1.8 (1) and 1.9 (1)] (Corollary 7.2 and Theorem 7.1).

**The algorithm** (`BHSV25.Alg.clusterAlg` with `m` clusters, `m` the number of distinct rows of
`M`, and uncolored vertices marked `k`) depends only on `M` and `π`: a rational threshold `θ`, the
net of `BHSV25.Net.exists_absNet` for the eigenvectors of `Ã` with `|μ| ≥ θ` (with `θ' = θ / 2` and
the bound `T = ⌊1 + 4 / θ'⁴⌋` of `BHSV25.Alg.card_abs_eig_ge_le`), of precision `κ / n` for a
rational `κ`. One algorithm thus serves every `ε`, as `BHSV25.SolvesExpanderColoring` asks.

**The analysis** (`BHSV25.Alg.expander_numColored`), on a regular `δ`-one-sided expander with an
`(M, δ)`-coloring `χ` whose monochromatic edges are covered by a set `S` of `δ n` vertices:

* the degree is positive (the model of an edgeless graph is `0`, far from `M`);
* the part sizes are within `C δ n` of `π n` ([BHSV25, Lemma 7.3],
  `BHSV25.Alg.exists_stationary_stable`), since the fractions `p_a = |V_a| / n` are exactly
  stationary for the model of `χ`;
* the contracted partition `χ'` (merging the parts with equal rows of `M`) has parts of at least
  `min π / 2 · n` vertices, weight at most `(2 + k) δ n` inside its parts, and a model whose rows
  are `αN / 2`-separated (`BHSV25.Alg.exists_sep_contracted`, `BHSV25.Alg.pmodel_contract_close`);
* with `L = √δ` as the upper bound on the second eigenvalue, Theorem 5.1
  (`BHSV25.Alg.exists_good_candidate`) gives a candidate agreeing with `χ'` on all but
  `E n = O_M(√δ) n` vertices;
* rounding each cluster against the part of its representative minus `S` colors all but
  `(α + O_M(δ) + 2 δ + 2 E) n` vertices (`BHSV25.Alg.numColored_ge_contract`,
  `BHSV25.Alg.sub_sum_max_le_alpha`).

The bounds hold for every `n`, so for each `ε` a small enough `δ` works on all graphs: the net's
error `κ / n` spoils no vertex when `512 m² κ² < α²` (see `BHSV25/Alg/Partition.lean`).

**Theorem 1.8 (1)** is the case of distinct rows, where `α = 0` (`BHSV25.Alg.alpha_eq_zero`), with
a stationary distribution obtained by normalizing the one of `BHSV25.IsModel`.
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Finset Matrix Turing.MultiTapeTM

variable {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} {π : Fin k → ℝ}

theorem numEigGT_anti (G : Graph) {a b : ℝ} (hab : a ≤ b) : G.numEigGT b ≤ G.numEigGT a :=
  card_le_card fun i hi ↦ by
    rw [mem_filter] at hi ⊢
    exact ⟨hi.1, lt_of_le_of_lt hab hi.2⟩

open Classical in
theorem pmodel_eq_zero_of_degree_zero {G : Graph} (h : G.2.IsRegularOfDegree 0)
    (χ : Fin G.1 → Fin k) (a b : Fin k) : pmodel G χ a b = 0 := by
  have h0 : ∀ x y, G.normAdj x y = 0 := fun x y ↦ by
    rw [G.normAdj_of_isRegularOfDegree h]
    split_ifs <;> simp
  simp [pmodel, wt, h0]

/-- **The analysis of the algorithm of Theorem 7.1**: on a regular `δ`-one-sided expander with an
`(M, δ)`-coloring, the algorithm colors all but `(α + m (2k + 2) C δ + 2 δ + 2 E) n` vertices,
where `E` is the error of Theorem 5.1 for the contracted partition. -/
theorem expander_numColored (hM : IsModel M) (hπ : IsStationary M π) (hk : 0 < k) {C : ℝ}
    (hC : 0 < C)
    (hstab : ∀ (p : Fin k → ℝ) (ε : ℝ), ∑ a, p a = 1 →
      (∀ b, |∑ a, p a * M a b - p b| ≤ ε) → ∀ a, |p a - π a| ≤ C * ε)
    {αN : ℝ} (hαN : 0 < αN)
    (hsepN : ∀ i j : Reps M π, i ≠ j → ∃ l : Reps M π,
      αN ≤ |∑ b ∈ rowGroup M l.1, M i.1 b - ∑ b ∈ rowGroup M l.1, M j.1 b|)
    {πmin : ℝ} (hπmin : 0 < πmin) (hπle : ∀ a, πmin ≤ π a)
    {θ : ℝ} (hθ : 0 < θ) (hθα : (2 * θ) ^ 2 * (2 / (πmin / 2)) ≤ (αN / 2) ^ 2 / 2)
    {κ : ℚ} (hκ : 512 * (Fintype.card (Reps M π) : ℝ) ^ 2 * (κ : ℝ) ^ 2 < (αN / 2) ^ 2)
    (net : ℕ × List Bool → List (List ℚ))
    {δ : ℝ} (hδ0 : 0 < δ) (hδk : k * δ < 1) (hδC : C * δ ≤ πmin / 2)
    (hδN : 2 * k * δ ≤ αN / 2)
    (hE : 512 * (Fintype.card (Reps M π) : ℝ) ^ 4 * ((2 + k) * δ / Real.sqrt δ + Real.sqrt δ) /
      (πmin / 2 * (2 * θ - θ) ^ 2 * (αN / 2) ^ 2) < πmin / 2)
    (G : Graph) (hreg : G.IsRegular) (hexp : G.numEigGT δ ≤ 1) (hcol : G.MColorable M δ)
    (hnet : ∀ w : Fin G.1 → ℝ, w ⬝ᵥ w ≤ 1 → G.InEigSpan (fun μ ↦ θ ≤ |μ|) w →
      ∃ u ∈ net (G.1, adjTable G), (Net.vecOf G.1 u - w) ⬝ᵥ (Net.vecOf G.1 u - w) ≤
        (κ / G.1) ^ 2) :
    (1 - (alpha M π + (Fintype.card (Reps M π) * ((2 * k + 2) * (C * δ)) + 2 * δ +
      2 * (512 * (Fintype.card (Reps M π) : ℝ) ^ 4 * ((2 + k) * δ / Real.sqrt δ + Real.sqrt δ) /
        (πmin / 2 * (2 * θ - θ) ^ 2 * (αN / 2) ^ 2))))) * G.1 ≤
      G.numColored k (clusterAlg (Fintype.card (Reps M π)) k net (G.1, adjTable G)) := by
  classical
  obtain ⟨χ, hmod, S, hScard, hS⟩ := hcol
  set m := Fintype.card (Reps M π) with hmdef
  set E := 512 * (m : ℝ) ^ 4 * ((2 + k) * δ / Real.sqrt δ + Real.sqrt δ) /
    (πmin / 2 * (2 * θ - θ) ^ 2 * (αN / 2) ^ 2) with hEdef
  have hm : 0 < m := Fintype.card_pos_iff.2 ⟨toRep M π ⟨0, hk⟩⟩
  have hmk : m ≤ k := (Fintype.card_subtype_le _).trans (by simp)
  have hmod' : ∀ a b, |M a b - pmodel G χ a b| ≤ δ := hmod
  rcases Nat.eq_zero_or_pos G.1 with hn0 | hn
  · rw [hn0, Nat.cast_zero, mul_zero]
    exact Nat.cast_nonneg _
  have hnR : (0 : ℝ) < G.1 := by exact_mod_cast hn
  obtain ⟨d, hd⟩ := hreg
  -- the degree is positive
  have hd0 : d ≠ 0 := by
    rintro rfl
    have hrow := hM.rowSum ⟨0, hk⟩
    have hle : ∑ b, M ⟨0, hk⟩ b ≤ ∑ _b : Fin k, δ := sum_le_sum fun b _ ↦ by
      have := hmod' ⟨0, hk⟩ b
      rw [pmodel_eq_zero_of_degree_zero hd, sub_zero] at this
      exact (le_abs_self _).trans this
    rw [hrow] at hle
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
    linarith
  -- the part sizes are close to `π`
  set s : Fin k → ℝ := fun a ↦ ((part G χ a).card : ℝ) with hsdef
  have hs : ∑ a, s a = G.1 := sum_card_part χ
  have hclose : ∀ a, |s a / G.1 - π a| ≤ C * δ := by
    refine hstab (fun a ↦ s a / G.1) δ ?_ ?_
    · rw [← sum_div, hs, div_self hnR.ne']
    · intro b
      have hst' : ∑ a, s a * pmodel G χ a b = s b := sum_card_mul_pmodel hd hd0 χ b
      have h3 : (∑ a, s a * pmodel G χ a b) / G.1 = s b / G.1 := by rw [hst']
      have h4 : ∑ a, s a / G.1 * pmodel G χ a b = (∑ a, s a * pmodel G χ a b) / G.1 := by
        rw [sum_div]
        exact sum_congr rfl fun a _ ↦ by ring
      have h5 : ∑ a, s a / G.1 * (M a b - pmodel G χ a b) =
          ∑ a, s a / G.1 * M a b - ∑ a, s a / G.1 * pmodel G χ a b := by
        simp only [mul_sub, sum_sub_distrib]
      have e1 : ∑ a, s a / G.1 * M a b - s b / G.1 =
          ∑ a, s a / G.1 * (M a b - pmodel G χ a b) := by
        linarith
      rw [e1]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ a, |s a / G.1 * (M a b - pmodel G χ a b)| ≤ ∑ a, s a / G.1 * δ :=
            sum_le_sum fun a _ ↦ by
              rw [abs_mul, abs_of_nonneg (by positivity)]
              exact mul_le_mul_of_nonneg_left (hmod' a b) (by positivity)
        _ = δ := by rw [← sum_mul, ← sum_div, hs, div_self hnR.ne', one_mul]
  have hsize0 : ∀ a, πmin / 2 * G.1 ≤ s a := by
    intro a
    have h := hclose a
    have h1 : π a - C * δ ≤ s a / G.1 := by linarith [neg_abs_le (s a / G.1 - π a)]
    have h2 : πmin / 2 ≤ s a / G.1 := by linarith [hπle a]
    rwa [le_div_iff₀ hnR] at h2
  -- the contracted partition
  set χ' := contract M π χ with hχ'
  have hsize : ∀ i : Reps M π, πmin / 2 * G.1 ≤ (part G χ' i).card := by
    intro i
    refine (hsize0 i.1).trans ?_
    change ((part G χ i.1).card : ℝ) ≤ (part G (contract M π χ) i).card
    exact_mod_cast card_le_card (part_subset_part_contract χ i)
  have hne : ∀ i : Reps M π, (part G χ' i).Nonempty := by
    intro i
    have : (0 : ℝ) < (part G χ' i).card := lt_of_lt_of_le (by positivity) (hsize i)
    exact card_pos.1 (by exact_mod_cast this)
  have hint : intWt G χ' ≤ (2 + k) * δ * G.1 := by
    have h1 := intWt_contract_le (π := π) hM χ hδ0.le hmod'
    have h2 := intWt_le_of_cover hd χ S hS
    linarith
  have hsep : ∀ i j : Reps M π, i ≠ j →
      (αN / 2) ^ 2 ≤ ∑ l, (pmodel G χ' i l - pmodel G χ' j l) ^ 2 := by
    intro i j hij
    obtain ⟨l, hl⟩ := hsepN i j hij
    have hi := pmodel_contract_close χ hmod' i l (hne i)
    have hj := pmodel_contract_close χ hmod' j l (hne j)
    have hdiff : αN / 2 ≤ |pmodel G χ' i l - pmodel G χ' j l| := by
      have := abs_sub_abs_le_abs_sub
        (∑ b ∈ rowGroup M l.1, M i.1 b - ∑ b ∈ rowGroup M l.1, M j.1 b)
        (pmodel G χ' i l - pmodel G χ' j l)
      have e : ∑ b ∈ rowGroup M l.1, M i.1 b - ∑ b ∈ rowGroup M l.1, M j.1 b -
          (pmodel G χ' i l - pmodel G χ' j l) =
          -(pmodel G χ' i l - ∑ b ∈ rowGroup M l.1, M i.1 b) +
            (pmodel G χ' j l - ∑ b ∈ rowGroup M l.1, M j.1 b) := by ring
      rw [e] at this
      have := this.trans (abs_add_le _ _)
      rw [abs_neg] at this
      linarith
    calc (αN / 2) ^ 2 ≤ |pmodel G χ' i l - pmodel G χ' j l| ^ 2 :=
          pow_le_pow_left₀ (by positivity) hdiff 2
      _ = (pmodel G χ' i l - pmodel G χ' j l) ^ 2 := sq_abs _
      _ ≤ ∑ l, (pmodel G χ' i l - pmodel G χ' j l) ^ 2 :=
          single_le_sum (fun l _ ↦ sq_nonneg (pmodel G χ' i l - pmodel G χ' j l)) (mem_univ l)
  -- the upper bound `√δ` on the second eigenvalue
  have hδ1 : δ < 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hsqrt0 : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  have hsqrt1 : Real.sqrt δ < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith
  have hδsqrt : δ ≤ Real.sqrt δ := by
    have := Real.sqrt_le_sqrt (le_of_lt hδ1)
    rw [Real.sqrt_one] at this
    nlinarith [Real.mul_self_sqrt hδ0.le]
  have hexpL : G.numEigGT (Real.sqrt δ) ≤ 1 := (numEigGT_anti G hδsqrt).trans hexp
  -- Theorem 5.1
  obtain ⟨us, hus, xs, hcount⟩ := exists_good_candidate hd hd0 χ' (Fintype.equivFin (Reps M π))
    hn (by positivity) hsize (by positivity) hsep hsqrt0 hsqrt1 hexpL hint
    (by linarith : θ < 2 * θ) hθα (net (G.1, adjTable G)) hnet hκ hE
  set B := univ.filter fun y : Fin G.1 ↦ clusterIdx (List.ofFn us)
    (List.ofFn fun j ↦ (xs j : ℕ)) y ≠ Fintype.equivFin (Reps M π) (χ' y) with hB
  have hBy : ∀ y, y ∉ B → clusterIdx (List.ofFn us) (List.ofFn fun j ↦ (xs j : ℕ)) y =
      Fintype.equivFin (Reps M π) (contract M π χ y) := by
    intro y hy
    rw [hB, mem_filter] at hy
    push Not at hy
    exact hy (mem_univ y)
  -- the accounting
  have hacc := numColored_ge_contract G χ S hS hm hmk (Fintype.equivFin (Reps M π)) net us hus
    xs B hBy
  have hcardc : ∀ i : Reps M π,
      ((part G (contract M π χ) i).card : ℝ) = ∑ a ∈ rowGroup M i.1, s a :=
    fun i ↦ card_part_contract χ i
  simp only [hcardc] at hacc
  have halpha := sub_sum_max_le_alpha (M := M) hπ.1 G.1 s hs (by positivity) hclose hn
  have hSn : (S.card : ℝ) ≤ δ * G.1 := hScard
  have hBn : (B.card : ℝ) ≤ E * G.1 := hcount
  nlinarith

/-! ### The theorems -/

/-- Without colors, only the empty graph is colorable, and the empty output is a coloring. -/
theorem expanderColoring_zero (hk : k = 0) (β : ℝ) :
    ∃ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring ∧
      SolvesExpanderColoring M β A := by
  refine ⟨fun _ ↦ [], ComputableInPolyTime.const _, fun ε _ ↦ ⟨1, one_pos, fun G _ _ hcol ↦ ?_⟩⟩
  obtain ⟨χ, -⟩ := hcol
  have hn : G.1 = 0 := by
    by_contra h
    have := (χ ⟨0, Nat.pos_of_ne_zero h⟩).2
    omega
  refine ⟨fun u _ _ _ ↦ absurd u.2 (by omega), ?_⟩
  rw [hn, Nat.cast_zero, mul_zero]
  exact Nat.cast_nonneg _

/-! ### The parameters -/

/-- The error of Theorem 5.1 for the contracted partition is `K₁ √δ`. -/
theorem error_eq_mul_sqrt (A D : ℝ) (k : ℕ) (δ : ℝ) :
    A * ((2 + k) * δ / Real.sqrt δ + Real.sqrt δ) / D = A * (3 + k) / D * Real.sqrt δ := by
  have h : (2 + (k : ℝ)) * δ / Real.sqrt δ = (2 + k) * Real.sqrt δ := by
    rw [mul_div_assoc, Real.div_sqrt]
  rw [h]
  ring

/-- **The choice of `δ`** for a given `ε`. -/
theorem exists_delta {k m : ℕ} (hk : 0 < k) {C αN πmin θ' K₁ ε : ℝ} (hC : 0 < C)
    (hαN : 0 < αN) (hπmin : 0 < πmin) (hθ' : 0 < θ') (hK₁ : 0 ≤ K₁) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ k * δ < 1 ∧ δ < θ' ^ 2 / 2 ∧ C * δ ≤ πmin / 2 ∧ 2 * k * δ ≤ αN / 2 ∧
      K₁ * Real.sqrt δ < πmin / 2 ∧
      m * ((2 * k + 2) * (C * δ)) + 2 * δ + 2 * (K₁ * Real.sqrt δ) ≤ ε := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set K₂ := m * ((2 * k + 2) * C) + 2 + 2 * K₁ with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  set t := min ε (πmin / 2) / (K₂ + K₁ + 1) with ht
  have ht0 : 0 < t := by positivity
  set δ : ℝ := min (min (1 / (2 * (k : ℝ))) (θ' ^ 2 / 4))
    (min (min (πmin / (2 * C)) (αN / (4 * k))) (t ^ 2)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / (2 * k) := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ θ' ^ 2 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ πmin / (2 * C) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ4 : δ ≤ αN / (4 * k) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ5 : δ ≤ t ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hδk : k * δ < 1 := by
    have h1 := mul_le_mul_of_nonneg_left hδ1 (by positivity : (0 : ℝ) ≤ k)
    have e : (k : ℝ) * (1 / (2 * k)) = 1 / 2 := by field_simp
    linarith
  have hδlt1 : δ < 1 := by
    have : δ ≤ k * δ := le_mul_of_one_le_left hδ0.le hkR
    linarith
  have hsq : Real.sqrt δ ≤ t := by
    calc Real.sqrt δ ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt hδ5
      _ = t := Real.sqrt_sq ht0.le
  have hδsq : δ ≤ Real.sqrt δ := by
    have h1 : Real.sqrt δ ≤ 1 := Real.sqrt_le_one.2 hδlt1.le
    have h2 := Real.mul_self_sqrt hδ0.le
    have h3 : Real.sqrt δ * Real.sqrt δ ≤ Real.sqrt δ * 1 :=
      mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg δ)
    linarith
  have htK : (K₂ + K₁ + 1) * t ≤ min ε (πmin / 2) := by
    rw [ht, mul_div_cancel₀ _ (by positivity)]
  have hexp : (K₂ + K₁ + 1) * t = K₂ * t + K₁ * t + t := by ring
  have hmin1 := min_le_left ε (πmin / 2)
  have hmin2 := min_le_right ε (πmin / 2)
  have hK₂t : 0 ≤ K₂ * t := by positivity
  have hK₁t : 0 ≤ K₁ * t := by positivity
  have hK₁s : K₁ * Real.sqrt δ ≤ K₁ * t := mul_le_mul_of_nonneg_left hsq hK₁
  have hK₂s : K₂ * Real.sqrt δ ≤ K₂ * t := mul_le_mul_of_nonneg_left hsq hK₂0
  refine ⟨δ, hδ0, hδk, ?_, ?_, ?_, ?_, ?_⟩
  · have : 0 < θ' ^ 2 := by positivity
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hδ3 hC.le
    have e : C * (πmin / (2 * C)) = πmin / 2 := by field_simp
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hδ4 (by positivity : (0 : ℝ) ≤ 2 * k)
    have e : 2 * (k : ℝ) * (αN / (4 * k)) = αN / 2 := by field_simp; ring
    linarith
  · linarith
  · have h1 : (m : ℝ) * ((2 * k + 2) * C) * δ ≤ m * ((2 * k + 2) * C) * Real.sqrt δ :=
      mul_le_mul_of_nonneg_left hδsq (by positivity)
    have e1 : (m : ℝ) * ((2 * k + 2) * (C * δ)) = m * ((2 * k + 2) * C) * δ := by ring
    have e2 : K₂ * Real.sqrt δ = m * ((2 * k + 2) * C) * Real.sqrt δ + 2 * Real.sqrt δ +
        2 * (K₁ * Real.sqrt δ) := by rw [hK₂]; ring
    linarith

/-- **The threshold `θ`**: a rational in `(0, 1/2)` with `(2 θ)² (2 / c) ≤ α² / 2`. -/
theorem exists_theta {αN πmin : ℝ} (hαN : 0 < αN) (hπmin : 0 < πmin) :
    ∃ θ : ℚ, (0 : ℝ) < θ ∧ (θ : ℝ) < 1 / 2 ∧
      (2 * (θ : ℝ)) ^ 2 * (2 / (πmin / 2)) ≤ (αN / 2) ^ 2 / 2 := by
  have hsqc : 0 < Real.sqrt (πmin / 2) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨θ, hθ0, hθ1⟩ : ∃ θ : ℚ, (0 : ℝ) < θ ∧
      (θ : ℝ) < min (1 / 2) (αN * Real.sqrt (πmin / 2) / 8) :=
    exists_rat_btwn (lt_min (by norm_num) (by positivity))
  refine ⟨θ, hθ0, lt_of_lt_of_le hθ1 (min_le_left _ _), ?_⟩
  have h1 : (θ : ℝ) ≤ αN * Real.sqrt (πmin / 2) / 8 :=
    (lt_of_lt_of_le hθ1 (min_le_right _ _)).le
  have h2 : (θ : ℝ) ^ 2 ≤ (αN * Real.sqrt (πmin / 2) / 8) ^ 2 := pow_le_pow_left₀ hθ0.le h1 2
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)] at h2
  have e1 : (2 * (θ : ℝ)) ^ 2 * (2 / (πmin / 2)) = 16 * (θ : ℝ) ^ 2 / πmin := by
    field_simp
    ring
  rw [e1, div_le_iff₀ hπmin]
  have e2 : (αN / 2) ^ 2 / 2 * πmin = 16 * (αN ^ 2 * (πmin / 2) / 8 ^ 2) := by ring
  rw [e2]
  linarith

/-- **The precision `κ`**: a positive rational with `512 m² κ² < α²`. -/
theorem exists_kappa {m : ℕ} (hm : 0 < m) {αN : ℝ} (hαN : 0 < αN) :
    ∃ κ : ℚ, (0 : ℝ) < κ ∧ 512 * (m : ℝ) ^ 2 * (κ : ℝ) ^ 2 < (αN / 2) ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨κ, hκ0, hκ1⟩ : ∃ κ : ℚ, (0 : ℝ) < κ ∧ (κ : ℝ) < αN / (64 * m) :=
    exists_rat_btwn (by positivity)
  refine ⟨κ, hκ0, ?_⟩
  have h1 : (κ : ℝ) ^ 2 < (αN / (64 * m)) ^ 2 := pow_lt_pow_left₀ hκ1 hκ0.le (by norm_num)
  have h2 : 512 * (m : ℝ) ^ 2 * (αN / (64 * m)) ^ 2 = αN ^ 2 / 8 := by
    field_simp
    ring
  have h3 : 512 * (m : ℝ) ^ 2 * (κ : ℝ) ^ 2 < 512 * (m : ℝ) ^ 2 * (αN / (64 * m)) ^ 2 :=
    mul_lt_mul_of_pos_left h1 (by positivity)
  have h4 : (αN / 2) ^ 2 = αN ^ 2 / 4 := by ring
  have h5 : 0 < αN ^ 2 := by positivity
  linarith

/-- **Theorem 1.9 (1)** of [BHSV25] (Theorem 7.1): for every model `M` with stationary
distribution `π`, a polynomial-time algorithm solves `(M, α)`-expander-coloring, where
`α = ∑_a min(π_a, ∑_{b ≠ a, M^(b) = M^(a)} π_b)`. -/
theorem expanderColoring_algorithm {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsModel M)
    (π : Fin k → ℝ) (hπ : IsStationary M π) :
    ∃ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring ∧
      SolvesExpanderColoring M (alpha M π) A := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · exact expanderColoring_zero hk0 _
  obtain ⟨C, hC, hstab⟩ := exists_stationary_stable M hM hπ
  obtain ⟨αN, hαN, hsepN⟩ := exists_sep_contracted (M := M) hπ
  have hne : (univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, mem_univ _⟩
  set πmin := univ.inf' hne π with hπmin_def
  have hπmin : 0 < πmin := (lt_inf'_iff _).2 fun a _ ↦ hπ.1 a
  have hπle : ∀ a, πmin ≤ π a := fun a ↦ inf'_le _ (mem_univ a)
  set m := Fintype.card (Reps M π) with hmdef
  have hm : 0 < m := Fintype.card_pos_iff.2 ⟨toRep M π ⟨0, hk⟩⟩
  have hmk : m ≤ k := (Fintype.card_subtype_le _).trans (by simp)
  obtain ⟨θ, hθ0, hθhalf, hθα⟩ := exists_theta hαN hπmin
  obtain ⟨κ, hκ0, hκ⟩ := exists_kappa hm hαN
  -- the net
  have hθ0' : (0 : ℚ) < θ := by exact_mod_cast hθ0
  have hκ0' : (0 : ℚ) < κ := by exact_mod_cast hκ0
  have hθ1' : θ ≤ 1 := by
    have : (θ : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have hθ'R : ((θ / 2 : ℚ) : ℝ) = θ / 2 := by push_cast; ring
  have hθ'0 : (0 : ℝ) < ((θ / 2 : ℚ) : ℝ) := by rw [hθ'R]; positivity
  have hθ'1 : ((θ / 2 : ℚ) : ℝ) < 1 := by rw [hθ'R]; linarith
  obtain ⟨net, hnetpoly, hnetcov⟩ := Net.exists_absNet (θ / 2) θ κ (by positivity)
    (by linarith) hθ1' hκ0' ⌊1 + 4 / ((θ / 2 : ℚ) : ℝ) ^ 4⌋₊
  refine ⟨fun G ↦ clusterAlg m k net (G.1, adjTable G), clusterAlg_graph_polytime m k hnetpoly,
    fun ε hε ↦ ?_⟩
  -- the choice of `δ`
  set K₁ := 512 * (m : ℝ) ^ 4 * (3 + k) / (πmin / 2 * (2 * (θ : ℝ) - θ) ^ 2 * (αN / 2) ^ 2)
    with hK₁
  have hK₁0 : 0 ≤ K₁ := by
    rw [hK₁]
    positivity
  obtain ⟨δ, hδ0, hδk, hδθ, hδC, hδN, hE, herr⟩ :=
    exists_delta (m := m) hk hC hαN hπmin hθ'0 hK₁0 hε
  have hEeq := error_eq_mul_sqrt (512 * (m : ℝ) ^ 4)
    (πmin / 2 * (2 * (θ : ℝ) - θ) ^ 2 * (αN / 2) ^ 2) k δ
  refine ⟨δ, hδ0, fun G hreg hexp hcol ↦ ⟨(clusterAlg_spec G hm hmk net).1, ?_⟩⟩
  -- the net covers the eigenspace
  have hcard : (univ.filter fun i ↦ ((θ / 2 : ℚ) : ℝ) ≤ |G.eig i|).card ≤
      ⌊1 + 4 / ((θ / 2 : ℚ) : ℝ) ^ 4⌋₊ :=
    Nat.le_floor (card_abs_eig_ge_le G hθ'0 hθ'1 hδθ hexp)
  have hmain := expander_numColored hM hπ hk hC hstab hαN hsepN hπmin hπle hθ0 hθα hκ net hδ0
    hδk hδC hδN (by rw [hEeq]; exact hE) G hreg hexp hcol (hnetcov G hreg hcard)
  rw [hEeq] at hmain
  have hn : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
  have : (1 - (alpha M π + ε)) * G.1 ≤ (1 - (alpha M π + ((m : ℝ) * ((2 * k + 2) * (C * δ)) +
      2 * δ + 2 * (K₁ * Real.sqrt δ)))) * G.1 :=
    mul_le_mul_of_nonneg_right (by linarith) hn
  exact this.trans hmain

/-- **Theorem 1.8 (1)** of [BHSV25] (Corollary 7.2): for every model `M` without repeated rows, a
polynomial-time algorithm solves `M`-expander-coloring. -/
theorem expanderColoring_distinctRows {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsModel M)
    (hrows : Function.Injective M) :
    ∃ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring ∧
      SolvesExpanderColoring M 0 A := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · exact expanderColoring_zero hk0 0
  obtain ⟨π, hπ⟩ := exists_isStationary_of_ne_zero M hM hk.ne'
  have h := expanderColoring_algorithm M hM π hπ
  rwa [alpha_eq_zero hπ.1 hrows] at h

end Alg

end BHSV25
