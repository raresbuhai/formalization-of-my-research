module

public import BHSV25.Hard.Corollaries
public import BHSV25.Hard.MachineA
public import BHSV25.Hard.Rate

/-!
# Theorem 1.5 with `λ₂ = o(1)`

[BHSV25, Corollary 8.4], in the form of `BHSV25.threeColoring_unbalanced_hardness`
(`BHSV25.Hard.threeColoring_unbalanced_hardness`): the reduction of Theorem 1.9 (2)
(`BHSV25/Hard/Model.lean`) for the model `M3 = [[0, 1/2, 1/2], [1, 0, 0], [1, 0, 0]]`, with the
precision of the template growing with the input (`BHSV25.Hard.Design.redA`).

* **Exact weights**: for `M3` and a precision `D = 4c`, the weights `⌊D π_i M_ij⌋` are exact, so
  the planted matrix of the design is exactly `κ M_ij / π_j` (`BHSV25.Hard.M3_exact`), and the
  blow-up is a one-sided expander up to the errors of the template and of the input graph alone,
  `(2 D 8^r + 2 m η) / 2^a` (`BHSV25.Hard.ModelRed.Data.isOneSidedExpander_exact`): both are
  divided by the degree of the template, at least `2^a`.
* **The rate**: at precision `a = a₀ + ⌈log₂ n⌉`, `2^a ≥ n`, and the blow-up has at most
  `b n^{2r+1}` vertices, so the second eigenvalue is at most `c (b / N)^{1/(2r+1)}` on `N`
  vertices (`BHSV25.Hard.rate`), which tends to `0`.
* The coloring and the no-instances are those of Theorem 1.9 (2), at the fixed precision `a₀`
  and maximum degree `η n` that make the model close to `M3`.
-/

@[expose] public section

namespace BHSV25.Hard

open Finset Turing.MultiTapeTM Cslib.Complexity Filter Topology

namespace ModelRed.Data

variable (X : Data)

theorem two_pow_le_deg (a : ℕ) : (2 : ℝ) ^ a ≤ X.design.deg a := by
  rw [X.deg_eq a]
  have hP : (1 : ℝ) ≤ X.P := by exact_mod_cast X.one_le_P
  have hc : (1 : ℝ) ≤ X.cnt := by exact_mod_cast X.one_le_cnt
  have hr : X.r ≠ 0 := by
    have hD : 0 < X.D := by
      have h := X.hD ⟨0, X.one_le_k⟩
      have := X.π_le_one ⟨0, X.one_le_k⟩
      by_contra hc
      have : (X.D : ℝ) = 0 := by exact_mod_cast Nat.eq_zero_of_not_pos hc
      nlinarith
    have hP0 : 0 < X.P := by
      have := X.one_le_P
      exact_mod_cast (show (0 : ℝ) < X.P by linarith)
    unfold r
    exact Nat.pos_iff_ne_zero.1 (Nat.mul_pos (Nat.mul_pos hP0 hP0) hD)
  have h1 : (2 : ℝ) ^ a ≤ 4 ^ a := pow_le_pow_left₀ (by norm_num) (by norm_num) a
  have h2 : (4 : ℝ) ^ a ≤ (4 ^ a) ^ X.r := le_self_pow₀ (one_le_pow₀ (by norm_num)) hr
  have h3 : (1 : ℝ) ≤ (X.P : ℝ) ^ 2 * X.cnt := by nlinarith
  have h4 : (0 : ℝ) ≤ ((4 : ℝ) ^ a) ^ X.r := by positivity
  nlinarith

/-- **The blow-up is a one-sided expander** when the weights are exact, with the bound
`(2 D 8^r + 2 m η) / 2^a`. -/
theorem isOneSidedExpander_exact (a : ℕ) (G : Graph) (hn : 0 < G.1) {η : ℝ} (hη : 0 ≤ η)
    (hdeg : G.MaxDegreeLE η)
    (hex : ∀ i j, (X.D : ℝ) * X.w i j / (X.s i * X.s j) = X.M i j / X.π j) {θ : ℝ}
    (hθ : (2 * X.D * 8 ^ X.r + 2 * X.m * η) / 2 ^ a ≤ θ) :
    (X.design.blow a G).IsOneSidedExpander θ := by
  classical
  have hΔ : ∀ v, ∑ v', ind (G.2.Adj v v') ≤ η * G.1 := fun v ↦ by
    rw [sum_ind_adj_eq_degree]; exact hdeg v
  have hn' : (0 : ℝ) < G.1 := by exact_mod_cast hn
  have hdr : (0 : ℝ) < X.design.deg a :=
    lt_of_lt_of_le (by positivity) (X.two_pow_le_deg a)
  have hd : 0 < X.design.deg a := by exact_mod_cast hdr
  have h := X.design.numEigGT_blow_le a G hn hd (by positivity) X.sum_abs_W0 hΔ
    (fun i j ↦ X.κ * (X.M i j / X.π j)) (le_refl 0) (fun i j ↦ ?_)
    (L := 1) (fun _ _ ↦ (1 : ℝ)) (fun Y hY ↦ ?_)
  · unfold Graph.IsOneSidedExpander
    refine le_trans (LowRank.numEigGT_anti _ ?_) h
    have hE := X.Eb_le a hn'.le (le_refl 0)
    have h2a := X.two_pow_le_deg a
    have hpa : (0 : ℝ) < 2 ^ a := by positivity
    rw [zero_mul, add_zero, div_le_iff₀ (by positivity)]
    have hθ' : (2 * X.D * 8 ^ X.r + 2 * X.m * η) / 2 ^ a * (X.design.deg a * G.1) ≤
        θ * (X.design.deg a * G.1) := mul_le_mul_of_nonneg_right hθ (by positivity)
    have hEta : 2 * (X.m : ℝ) * (η * G.1) / 2 ≤
        (X.m * η / 2 ^ a) * (X.design.deg a * G.1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpa]
      have : (0 : ℝ) ≤ X.m * η * G.1 := by positivity
      nlinarith
    have hsplit : (2 * X.D * 8 ^ X.r + 2 * X.m * η) / 2 ^ a * (X.design.deg a * G.1) =
        2 * ((X.D * 8 ^ X.r / 2 ^ a + X.m * 0) * (X.design.deg a * G.1)) +
          2 * ((X.m * η / 2 ^ a) * (X.design.deg a * G.1)) := by
      field_simp
      ring
    simp only [mul_zero, zero_mul, add_zero, mul_zero, zero_div] at hE
    nlinarith
  · rw [X.chat_eq, hex, sub_self, abs_zero]
  · have hY0 : ∑ i, Y i = 0 := by simpa using hY 0
    have := model_quad_nonpos X.hM X.hπ Y hY0
    have e : ∑ i, ∑ j, Y i * (X.κ * (X.M i j / X.π j)) * Y j =
        X.κ * ∑ i, ∑ j, Y i * (X.M i j / X.π j) * Y j := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [mul_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      ring
    rw [e]
    exact mul_nonpos_of_nonneg_of_nonpos X.κ_nonneg this

end ModelRed.Data

/-- **The weights of `M3` are exact** at a precision `4c`. -/
theorem M3_exact (c H m : ℕ) (hD : ∀ i, 2 * (3 : ℝ) + 1 ≤ (4 * c : ℕ) * π3 i) (hH : 0 < H)
    (hm : 0 < m) (i j : Fin 3) :
    let X : ModelRed.Data := ⟨3, M3, π3, isModel_M3, isStationary_M3, 4 * c, H, m, hD, hH, hm⟩
    ((X.D : ℝ) * X.w i j / (X.s i * X.s j) = X.M i j / X.π j) := by
  intro X
  have hc : (0 : ℝ) < c := by
    have := hD 0
    simp [π3] at this
    nlinarith
  have hw : ∀ i j, X.w i j = if (i = 0 ∧ j ≠ 0) ∨ (i ≠ 0 ∧ j = 0) then c else 0 := by
    intro i j
    simp only [X, ModelRed.Data.w]
    fin_cases i <;> fin_cases j <;> norm_num [M3, π3] <;> (try ring_nf) <;> simp
  have hs : ∀ i, (X.s i : ℝ) = if i = 0 then 2 * c else c := by
    intro i
    simp only [ModelRed.Data.s]
    rw [Fin.sum_univ_three]
    fin_cases i
    · simp [hw]; ring
    · simp [hw]
    · simp [hw]
  rw [hs, hs, hw]
  simp only [X]
  fin_cases i <;> fin_cases j <;> simp [M3, π3] <;> field_simp <;> ring

/-- **The rate of a design reduction**: at precision `a = a₀ + ⌈log₂ n⌉`, `c / 2^a` is at most
`c (b / N)^{1/(2r+1)}` for the number `N` of vertices of the output and
`b = |types| (8 · 4^{a₀})^r`. -/
theorem Design.div_two_pow_le_rate (D : Design) (a₀ : ℕ) {c : ℝ} (hc : 0 ≤ c) (G : Graph)
    (hn : 0 < G.1) (hT : 0 < D.nT) :
    c / 2 ^ Design.prec a₀ G.1 ≤
      rate c (D.nT * (8 * 4 ^ a₀) ^ D.r) (2 * D.r + 1) (D.redA a₀ G).1 := by
  set a := Design.prec a₀ G.1 with ha
  obtain ⟨hlo, hhi⟩ := pow_clog_bounds (n := G.1) hn
  have hn' : (0 : ℝ) < G.1 := by exact_mod_cast hn
  have h2a : (2 : ℝ) ^ a = 2 ^ a₀ * 2 ^ Nat.clog 2 G.1 := by
    rw [ha, Design.prec, pow_add]
  have hlo' : (G.1 : ℝ) ≤ 2 ^ a := by
    rw [h2a]
    have : (G.1 : ℝ) ≤ 2 ^ Nat.clog 2 G.1 := by exact_mod_cast hlo
    have h1 : (1 : ℝ) ≤ 2 ^ a₀ := one_le_pow₀ (by norm_num)
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) (Nat.clog 2 G.1)]
  have hup : (2 : ℝ) ^ a ≤ 2 ^ a₀ * (2 * G.1) := by
    rw [h2a]
    have : (2 : ℝ) ^ Nat.clog 2 G.1 ≤ 2 * G.1 := by exact_mod_cast hhi.le
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h1 : c / 2 ^ a ≤ c / G.1 := div_le_div_of_nonneg_left hc hn' hlo'
  have hN : (D.redA a₀ G).1 = D.nA a₀ G.1 := D.redA_fst a₀ G
  have hNeq : ((D.nA a₀ G.1 : ℕ) : ℝ) = (2 * (2 ^ a * 2 ^ a)) ^ D.r * D.nT * G.1 := by
    simp only [Design.nA, Design.cells, Design.base, ← ha]
    push_cast
    ring
  have hT' : (0 : ℝ) < D.nT := by exact_mod_cast hT
  have hNpos : 0 < D.nA a₀ G.1 := by
    have : (0 : ℝ) < D.nA a₀ G.1 := by rw [hNeq]; positivity
    exact_mod_cast this
  have hbase : 2 * ((2 : ℝ) ^ a * 2 ^ a) ≤ 8 * 4 ^ a₀ * (G.1 : ℝ) ^ 2 := by
    have h4 : (4 : ℝ) ^ a₀ = 2 ^ a₀ * 2 ^ a₀ := by rw [← mul_pow]; norm_num
    rw [h4]
    have h0 : (0 : ℝ) ≤ 2 ^ a := by positivity
    nlinarith
  have hpow : (2 * ((2 : ℝ) ^ a * 2 ^ a)) ^ D.r ≤ (8 * 4 ^ a₀) ^ D.r * (G.1 : ℝ) ^ (2 * D.r) := by
    calc (2 * ((2 : ℝ) ^ a * 2 ^ a)) ^ D.r ≤ (8 * 4 ^ a₀ * (G.1 : ℝ) ^ 2) ^ D.r :=
          pow_le_pow_left₀ (by positivity) hbase _
      _ = _ := by rw [mul_pow, pow_mul]
  have hNb : ((D.nA a₀ G.1 : ℕ) : ℝ) ≤ D.nT * (8 * 4 ^ a₀) ^ D.r * (G.1 : ℝ) ^ (2 * D.r + 1) := by
    rw [hNeq, pow_succ]
    have h0 : (0 : ℝ) ≤ D.nT * G.1 := by positivity
    nlinarith
  have h2 := div_le_rate hc (by omega : 2 * D.r + 1 ≠ 0) hn hNpos hNb
  rw [hN]
  linarith

/-- Theorem 1.5 for `ε ≤ 1/2 - γ`, with an `(M3, ε)`-coloring and `λ₂ = o(1)`. -/
theorem threeColoring_unbalanced_hardness_le (hUGC : UniqueGames.KhotUGC) {γ ε : ℝ}
    (hγ : 0 < γ) (hε : 0 < ε) (hεγ : ε ≤ 1 / 2 - γ) :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      PromiseProblem.NPHard encGraph (coloringGap (fun G ↦ G.IsRegular ∧
        G.IsOneSidedExpander (f G.1) ∧ G.MColorable M3 ε) 3 (1 / 2 - γ)) := by
  have hπpm : ∀ i, (1 / 4 : ℝ) ≤ π3 i := by intro i; fin_cases i <;> norm_num [π3]
  have hpm : (0 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨ε₀, hε₀, hBK⟩ := bansalKhot hUGC
  set εB := min ε₀ (ε / 8) with hεB
  set γB := min ε₀ (γ / (4 * 3)) with hγB
  have hεB0 : 0 < εB := lt_min hε₀ (by positivity)
  have hγB0 : 0 < γB := lt_min hε₀ (by positivity)
  have hεB8 : εB ≤ ε / 8 := min_le_right _ _
  have hγBk : (3 : ℝ) * γB ≤ γ / 4 := by
    have : γB ≤ γ / (4 * 3) := min_le_right _ _
    linarith
  -- the absorber blocks
  obtain ⟨m, hm1, hm⟩ : ∃ m : ℕ, 0 < m ∧ 1 / ((m : ℝ) + 1) ≤ ε / 4 := by
    obtain ⟨m₀, hm₀⟩ := exists_nat_gt (4 / ε)
    refine ⟨m₀ + 1, by omega, ?_⟩
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (4 / ε) * ε = 4 := by field_simp
    push_cast
    nlinarith
  -- the color units
  obtain ⟨H, hH1, hHpm, hHγ, hHε⟩ : ∃ H : ℕ, 0 < H ∧ (3 : ℝ) + 1 ≤ 2 * H * (1 / 4) ∧
      (3 : ℝ) / H ≤ γ / 4 ∧ (3 : ℝ) / (2 * H) ≤ ε * (1 / 4) / 8 := by
    obtain ⟨H₀, hH₀⟩ := exists_nat_gt (16 + 12 / γ + 48 / ε)
    have h2 : (0 : ℝ) ≤ 12 / γ := by positivity
    have h3 : (0 : ℝ) ≤ 48 / ε := by positivity
    have hH : (H₀ : ℝ) + 1 > 0 := by positivity
    refine ⟨H₀ + 1, by omega, ?_, ?_, ?_⟩ <;> push_cast
    · nlinarith
    · rw [div_le_iff₀ hH]
      have : 12 / γ ≤ (H₀ : ℝ) + 1 := by linarith
      rw [div_le_iff₀ hγ] at this
      linarith
    · rw [div_le_iff₀ (by positivity)]
      have : 48 / ε ≤ (H₀ : ℝ) + 1 := by linarith
      rw [div_le_iff₀ hε] at this
      nlinarith
  -- the precision of the weights, a multiple of `4`
  obtain ⟨c, hDπ, hDγ, hDε, hDδε⟩ : ∃ c : ℕ, 2 * (3 : ℝ) + 1 ≤ ((4 * c : ℕ) : ℝ) * (1 / 4) ∧
      2 * (3 : ℝ) ^ 2 / (4 * c : ℕ) ≤ γ / 4 ∧ (3 : ℝ) ^ 2 / (4 * c : ℕ) ≤ ε * (1 / 4) / 8 ∧
      8 * (3 : ℝ) / ((4 * c : ℕ) * (1 / 4) ^ 3) ≤ ε / 4 := by
    obtain ⟨D₀, hD₀⟩ := exists_nat_gt (28 + 72 / γ + 288 / ε + 6144 / ε)
    have h2 : (0 : ℝ) ≤ 72 / γ := by positivity
    have h3 : (0 : ℝ) ≤ 288 / ε := by positivity
    have h4 : (0 : ℝ) ≤ 6144 / ε := by positivity
    have hD : (0 : ℝ) < (D₀ : ℝ) + 1 := by positivity
    have hD4 : (D₀ : ℝ) + 1 ≤ 4 * ((D₀ : ℝ) + 1) := by linarith
    refine ⟨D₀ + 1, ?_, ?_, ?_, ?_⟩ <;> push_cast
    · nlinarith
    · rw [div_le_iff₀ (by positivity)]
      have : 72 / γ ≤ (D₀ : ℝ) + 1 := by linarith
      rw [div_le_iff₀ hγ] at this
      nlinarith
    · rw [div_le_iff₀ (by positivity)]
      have : 288 / ε ≤ (D₀ : ℝ) + 1 := by linarith
      rw [div_le_iff₀ hε] at this
      nlinarith
    · rw [div_le_iff₀ (by positivity)]
      have : 6144 / ε ≤ (D₀ : ℝ) + 1 := by linarith
      rw [div_le_iff₀ hε] at this
      nlinarith
  have hD : ∀ i, 2 * (3 : ℝ) + 1 ≤ ((4 * c : ℕ) : ℝ) * π3 i := fun i ↦
    hDπ.trans (mul_le_mul_of_nonneg_left (hπpm i) (Nat.cast_nonneg _))
  set X : ModelRed.Data := ⟨3, M3, π3, isModel_M3, isStationary_M3, 4 * c, H, m, hD, hH1, hm1⟩
    with hX
  -- the base precision and the maximum degree
  set T : ℝ := ε / 8 / (1 + 2 * H * (4 * c : ℕ)) with hT
  have hT0 : 0 < T := by positivity
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℕ, 2 * ((4 * c : ℕ) : ℝ) * 8 ^ X.r / 2 ^ a₀ ≤ T := by
    obtain ⟨a, ha⟩ :=
      pow_unbounded_of_one_lt (2 * ((4 * c : ℕ) : ℝ) * 8 ^ X.r / T) (by norm_num : (1 : ℝ) < 2)
    refine ⟨a, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hT0] at ha
    linarith
  set η : ℝ := T / (2 * m) with hη
  have hη0 : 0 < η := by positivity
  have hξ : ∀ a, a₀ ≤ a → X.ξ a η ≤ 2 * T := by
    intro a ha
    change 2 * ((4 * c : ℕ) : ℝ) * 8 ^ X.r / 2 ^ a + 2 * m * η ≤ 2 * T
    have h1 : 2 * ((4 * c : ℕ) : ℝ) * 8 ^ X.r / 2 ^ a ≤ 2 * ((4 * c : ℕ) : ℝ) * 8 ^ X.r / 2 ^ a₀ :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ (by norm_num) ha)
    have : 2 * (m : ℝ) * η = T := by simp only [hη]; field_simp
    linarith
  have hδ : X.δ₀ (1 / 4) ≤ ε / 4 := hDδε
  have hNP := hBK εB γB η hεB0 (min_le_left _ _) hγB0 (min_le_left _ _) hη0
  have hα : alpha M3 π3 = 1 / 2 := alpha_M3
  set cc : ℝ := 2 * ((4 * c : ℕ) : ℝ) * 8 ^ X.r + 2 * m * η with hcc
  have hcc0 : 0 ≤ cc := by positivity
  refine ⟨rate cc (X.design.nT * (8 * 4 ^ a₀) ^ X.design.r) (2 * X.design.r + 1),
    tendsto_rate _ _ (by omega), ?_⟩
  refine npHard_of_reduction hεB0.le hγB0 hη0.le hNP (X.design.redA a₀)
    (X.design.redA_polytime a₀) (fun G hG hn ↦ ?_) fun G hG ↦ ?_
  · -- yes-instances
    obtain ⟨hdeg, I, J, hIJ, hI, hJ, hIc, hJc⟩ := hG
    set a := Design.prec a₀ G.1
    have ha : a₀ ≤ a := Nat.le_add_right _ _
    have hcov : 1 / ((m : ℝ) + 1) + 2 * εB ≤ ε := by linarith
    have hmod : X.ξ a η * (1 + 2 * H * (4 * c : ℕ)) + X.δ₀ (1 / 4) +
        ((3 : ℝ) ^ 2 / (4 * c : ℕ) + 3 / (2 * H)) / (1 / 4) ≤ ε := by
      have h1 : X.ξ a η * (1 + 2 * H * (4 * c : ℕ)) ≤ ε / 4 := by
        have hpos : (0 : ℝ) < 1 + 2 * H * (4 * c : ℕ) := by positivity
        calc X.ξ a η * (1 + 2 * H * (4 * c : ℕ)) ≤ 2 * T * (1 + 2 * H * (4 * c : ℕ)) :=
              mul_le_mul_of_nonneg_right (hξ a ha) hpos.le
          _ = ε / 4 := by rw [hT]; field_simp; ring
      have h2 : ((3 : ℝ) ^ 2 / (4 * c : ℕ) + 3 / (2 * H)) / (1 / 4) ≤ ε / 4 := by
        rw [div_le_iff₀ hpm]
        linarith
      linarith
    obtain ⟨hreg, -, hcol⟩ := X.yes a G hn hη0.le hpm hπpm hHpm hdeg hIJ hI hJ hIc hJc hcov
      hmod (lam := X.ξ a η + X.δ₀ (1 / 4)) le_rfl
    have hC : 0 < Fintype.card (X.design.Cell a) := by
      have : (0 : ℝ) < Fintype.card (X.design.Cell a) := by
        rw [X.card_cells a]
        have : (1 : ℝ) ≤ ∑ i, (X.s i : ℝ) :=
          le_trans (by exact_mod_cast X.one_le_s ⟨0, by norm_num⟩)
            (single_le_sum (f := fun i ↦ (X.s i : ℝ)) (fun i _ ↦ Nat.cast_nonneg _)
              (mem_univ _))
        have := X.one_le_cnt
        positivity
      exact_mod_cast this
    have hT' : 0 < X.design.nT := by
      rw [Fintype.card_prod] at hC
      exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hC
    have hexp := X.isOneSidedExpander_exact a G hn hη0.le hdeg (M3_exact c H m hD hH1 hm1)
      (X.design.div_two_pow_le_rate a₀ hcc0 G hn hT')
    exact ⟨⟨hreg, hexp, hcol⟩, hasColoring_mono (hasColoring_of_mColorable _ hcol) hεγ⟩
  · -- no-instances
    have hn := pos_of_mem_no hγB0 hG
    obtain ⟨-, -, hno⟩ := hG
    set a := Design.prec a₀ G.1
    have hC : 0 < Fintype.card (X.design.Cell a) := by
      have : (0 : ℝ) < Fintype.card (X.design.Cell a) := by
        rw [X.card_cells a]
        have : (1 : ℝ) ≤ ∑ i, (X.s i : ℝ) :=
          le_trans (by exact_mod_cast X.one_le_s ⟨0, by norm_num⟩)
            (single_le_sum (f := fun i ↦ (X.s i : ℝ)) (fun i _ ↦ Nat.cast_nonneg _)
              (mem_univ _))
        have := X.one_le_cnt
        positivity
      exact_mod_cast this
    refine not_hasColoring_of_le (Nat.mul_pos hC hn) (q := 1 - alpha M3 π3 + 3 * γ / 4)
      (by linarith) fun c' hc' ↦ ?_
    have h := X.no a G hγB0.le hno c' hc'
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    change 1 - alpha M3 π3 + 2 * (3 : ℝ) ^ 2 / (4 * c : ℕ) + 3 / H + 3 * γB ≤
      1 - alpha M3 π3 + 3 * γ / 4
    linarith

/-- **Theorem 1.5** of [BHSV25] (Corollary 8.4). -/
theorem threeColoring_unbalanced_hardness (hUGC : UniqueGames.KhotUGC) :
    ∀ ε γ : ℝ, 0 < ε → 0 < γ → γ < 1 / 2 →
      ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
        PromiseProblem.NPHard encGraph (coloringGap (fun G ↦ G.IsRegular ∧
          G.IsOneSidedExpander (f G.1) ∧ G.HasColoring 3 ε) 3 (1 / 2 - γ)) := by
  intro ε γ hε hγ hγ2
  obtain ⟨f, hf, h⟩ := threeColoring_unbalanced_hardness_le hUGC (ε := min ε (1 / 2 - γ)) hγ
    (lt_min hε (by linarith)) (min_le_right _ _)
  refine ⟨f, hf, h.mono (fun G hG ↦ ⟨⟨hG.1.1, hG.1.2.1, hasColoring_mono
    (hasColoring_of_mColorable G hG.1.2.2) (min_le_left _ _)⟩, hG.2⟩) fun _ h ↦ h⟩

end BHSV25.Hard
