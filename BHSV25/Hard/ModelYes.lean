module

public import BHSV25.Hard.ModelEst
public import BHSV25.Hard.LowRank

/-!
# The design for Theorem 1.9 (2): yes-instances

For a yes-instance `G` of the gap problem of Bansal and Khot, with disjoint independent sets `I`,
`J` of `(1/2 - ε_B) n` vertices each and maximum degree `η n`, the blow-up `H` of the design of
`BHSV25/Hard/ModelDesign.lean` (`BHSV25.Hard.ModelRed.Data.yes`):

* is regular (`BHSV25.Hard.Design.blow_isRegular`);
* is a `λ`-one-sided expander (`BHSV25.Hard.ModelRed.Data.isOneSidedExpander`): its planted
  matrix is within `κ δ₀` of `κ M_ij / π_j`, which is at most `0` on the vectors of sum `0`
  (`BHSV25.Hard.model_quad_nonpos`);
* has the `(M, ε)`-coloring `χ` given by the labels of `BHSV25/Hard/ModelCount.lean`: its
  monochromatic edges are covered by the absorbers and the vertices of the copies outside
  `I ∪ J` (`BHSV25.Hard.ModelRed.Data.card_cover_le`), and its model is within `ε` of `M`
  (`BHSV25.Hard.ModelRed.Data.abs_model_sub_le`): by the bilinear approximation
  (`BHSV25.Hard.Design.bil_blow_sub_le`), the edges between the colors `c` and `e` number
  `κ (M_ce / π_e) |c| |e|` up to small errors, and `κ |e| / d` is the fraction `V_e ≈ π_e` of
  color `e`.
-/

@[expose] public section

namespace BHSV25.Hard

open Finset Matrix Cayley

open Classical in
/-- The model of a partition of a regular graph in terms of the bilinear form of its adjacency
matrix. -/
theorem model_eq_bil (G : Graph) {d : ℕ} (hreg : G.2.IsRegularOfDegree d) {k : ℕ}
    (χ : Fin G.1 → Fin k) (c e : Fin k) :
    G.model χ c e = bil G (fun p ↦ if χ p = c then 1 else 0) (fun q ↦ if χ q = e then 1 else 0) /
      (d * (univ.filter (χ · = c)).card) := by
  classical
  unfold Graph.model
  rw [← div_div]
  congr 1
  unfold bil
  rw [sum_div, sum_filter]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [sum_div, sum_filter]
  split_ifs with hp
  · refine sum_congr rfl fun q _ ↦ ?_
    rw [G.normAdj_of_isRegularOfDegree hreg]
    unfold ind
    by_cases hq : χ q = e <;> by_cases hadj : G.2.Adj p q <;> simp [hp, hq, hadj, div_eq_mul_inv]
  · simp [hp]

theorem dot_indicator {n k : ℕ} (χ : Fin n → Fin k) (c : Fin k) :
    (fun p ↦ if χ p = c then (1 : ℝ) else 0) ⬝ᵥ (fun p ↦ if χ p = c then (1 : ℝ) else 0) =
      (univ.filter (χ · = c)).card := by
  have h : ∀ p, (if χ p = c then (1 : ℝ) else 0) * (if χ p = c then (1 : ℝ) else 0) =
      if χ p = c then 1 else 0 := fun p ↦ by split_ifs <;> simp
  simp only [dotProduct, h]
  rw [sum_boole]

/-- The arithmetic of the model estimate. -/
theorem abs_model_arith {R πe B Q κ cc ce dR Eb δ V A T : ℝ} (hcc : 0 < cc) (hdR : 0 < dR)
    (hce : 0 ≤ ce) (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (h1 : |B - Q| ≤ Eb * (cc + ce)) (h2 : |Q - κ * R * cc * ce| ≤ κ * δ * cc * ce)
    (hV : κ * ce / dR = V) (hEb : Eb ≤ A * dR) (hratio : ce ≤ T * cc) (hV1 : V ≤ 1) :
    |R * πe - B / (dR * cc)| ≤ A * (1 + T) + δ + R * |V - πe| := by
  have hdc : 0 < dR * cc := mul_pos hdR hcc
  have hsplit : B / (dR * cc) - R * πe =
      (B - Q) / (dR * cc) + (Q - κ * R * cc * ce) / (dR * cc) + R * (V - πe) := by
    rw [← hV]; field_simp; ring
  have hV0 : 0 ≤ V := by rw [← hV]; positivity
  have e1 : |(B - Q) / (dR * cc)| ≤ A * (1 + T) := by
    rw [abs_div, abs_of_pos hdc, div_le_iff₀ hdc]
    calc |B - Q| ≤ Eb * (cc + ce) := h1
      _ ≤ A * dR * (cc + ce) := mul_le_mul_of_nonneg_right hEb (by positivity)
      _ ≤ A * dR * (cc + T * cc) := by gcongr
      _ = A * (1 + T) * (dR * cc) := by ring
  have e2 : |(Q - κ * R * cc * ce) / (dR * cc)| ≤ δ := by
    rw [abs_div, abs_of_pos hdc, div_le_iff₀ hdc]
    calc |Q - κ * R * cc * ce| ≤ κ * δ * cc * ce := h2
      _ = δ * V * (dR * cc) := by rw [← hV]; field_simp
      _ ≤ δ * 1 * (dR * cc) := by gcongr
      _ = δ * (dR * cc) := by ring
  rw [abs_sub_comm, hsplit]
  calc |(B - Q) / (dR * cc) + (Q - κ * R * cc * ce) / (dR * cc) + R * (V - πe)|
      ≤ |(B - Q) / (dR * cc)| + |(Q - κ * R * cc * ce) / (dR * cc)| + |R * (V - πe)| :=
        abs_add_three _ _ _
    _ ≤ A * (1 + T) + δ + R * |V - πe| := by
        rw [abs_mul, abs_of_nonneg hR]
        linarith

namespace ModelRed

open LowRank

namespace Data

variable (X : Data)

/-! ### The correction -/

theorem abs_W0_le (τ τ' : X.Ty) : |(X.W0 τ τ' : ℝ)| ≤
    zi (X.copy τ ∧ τ' = τ) + zi (X.absb τ ∧ X.absb τ' ∧ τ'.1 = τ.1 ∧ τ'.2.1 = τ.2.1) +
    zi (X.copy τ ∧ τ' = X.host τ) +
    zi (X.absb τ ∧ τ'.1 = X.swap τ.1 ∧ τ'.2.1 = τ.2.1 ∧ τ'.2.2.1 = τ.2.2.1 ∧
      τ'.2.2.2 ≠ Fin.last X.m) := by
  have h : |X.W0 τ τ'| ≤
      zi (X.copy τ ∧ τ' = τ) + zi (X.absb τ ∧ X.absb τ' ∧ τ'.1 = τ.1 ∧ τ'.2.1 = τ.2.1) +
      zi (X.copy τ ∧ τ' = X.host τ) +
      zi (X.absb τ ∧ τ'.1 = X.swap τ.1 ∧ τ'.2.1 = τ.2.1 ∧ τ'.2.2.1 = τ.2.2.1 ∧
        τ'.2.2.2 ≠ Fin.last X.m) := by
    unfold W0
    refine abs_le.2 ⟨?_, ?_⟩ <;>
      linarith [zi_nonneg (X.copy τ ∧ τ' = τ),
        zi_nonneg (X.absb τ ∧ X.absb τ' ∧ τ'.1 = τ.1 ∧ τ'.2.1 = τ.2.1),
        zi_nonneg (X.copy τ ∧ τ' = X.host τ),
        zi_nonneg (X.absb τ ∧ τ'.1 = X.swap τ.1 ∧ τ'.2.1 = τ.2.1 ∧ τ'.2.2.1 = τ.2.2.1 ∧
          τ'.2.2.2 ≠ Fin.last X.m)]
  have := (Int.cast_le (R := ℝ)).2 h
  push_cast at this
  exact this

theorem sum_abs_W0 (τ : X.Ty) : ∑ τ', |(X.W0 τ τ' : ℝ)| ≤ 2 * X.m := by
  have h : ∑ τ', (zi (X.copy τ ∧ τ' = τ) +
      zi (X.absb τ ∧ X.absb τ' ∧ τ'.1 = τ.1 ∧ τ'.2.1 = τ.2.1) +
      zi (X.copy τ ∧ τ' = X.host τ) +
      zi (X.absb τ ∧ τ'.1 = X.swap τ.1 ∧ τ'.2.1 = τ.2.1 ∧ τ'.2.2.1 = τ.2.2.1 ∧
        τ'.2.2.2 ≠ Fin.last X.m)) ≤ 2 * X.m := by
    simp only [sum_add_distrib]
    rw [X.sum_t1, X.sum_t2, X.sum_t3, X.sum_t4]
    have hm : (1 : ℤ) ≤ X.m := by exact_mod_cast X.hm
    by_cases hc : X.copy τ
    · rw [zi_of hc, zi_of_not (X.not_absb_of_copy hc)]; linarith
    · rw [zi_of_not hc]
      rcases (show zi (X.absb τ) = 0 ∨ zi (X.absb τ) = 1 by unfold zi; split_ifs <;> simp)
        with h | h <;> rw [h] <;> linarith
  have h' := (Int.cast_le (R := ℝ)).2 h
  push_cast at h'
  refine le_trans (sum_le_sum fun τ' _ ↦ X.abs_W0_le τ τ') ?_
  exact_mod_cast h'

/-! ### Cells and colors -/

variable (a : ℕ)

theorem card_cells_c₁ (b : Fin X.k) :
    (univ.filter fun u ↦ (X.labels a).c₁ u = b).card =
      (2 * 4 ^ a) ^ X.r * (univ.filter fun τ ↦ X.c₁ τ = b).card :=
  X.design.card_cells a (fun τ ↦ X.c₁ τ = b)

theorem card_cells_c₂ (b : Fin X.k) :
    (univ.filter fun u ↦ (X.labels a).c₂ u = b).card =
      (2 * 4 ^ a) ^ X.r * (univ.filter fun τ ↦ X.c₁ τ = b).card := by
  rw [← X.card_c₂ b]
  exact X.design.card_cells a (fun τ ↦ X.c₂ τ = b)

/-- **The color classes**: color `b` has `n Γ m (m + 1) ∑_j s_j ℓ_jb` vertices. -/
theorem card_class (G : Graph) (J : Finset (Fin G.1)) (b : Fin X.k) :
    ((univ.filter fun p ↦ (X.labels a).chi J p = b).card : ℝ) =
      G.1 * (2 * 4 ^ a) ^ X.r * (X.m * (X.m + 1) * ∑ j, (X.s j : ℝ) * X.ℓ j b) := by
  rw [(X.labels a).card_chi_of_sym J (fun b' ↦ by rw [card_cells_c₁, card_cells_c₂]) b,
    card_cells_c₁, ← X.card_c₁ b]
  push_cast
  ring

theorem row_chi (G : Graph) (J : Finset (Fin G.1)) (p : Fin (X.design.blow a G).1) :
    X.M ((X.labels a).chi J p) = X.M (X.design.grp a p) := by
  unfold Template.Labels.chi
  split_ifs
  · exact X.row_c₂ _
  · exact X.row_c₁ _

theorem card_cells : (Fintype.card (X.design.Cell a) : ℝ) =
    (∑ i, (X.s i : ℝ)) * X.cnt * (2 * 4 ^ a) ^ X.r := by
  rw [Design.card_cell]
  change ((Fintype.card X.Ty * (2 * 4 ^ a) ^ X.r : ℕ) : ℝ) = _
  rw [card_Ty]
  push_cast
  ring

/-! ### Scales -/

/-- The error of the bilinear approximation, relative to the degree. -/
noncomputable def ξ (η : ℝ) : ℝ := 2 * X.D * 8 ^ X.r / 2 ^ a + 2 * X.m * η

/-- The error of the planted matrix. -/
noncomputable def δ₀ (pm : ℝ) : ℝ := 8 * X.k / (X.D * pm ^ 3)

theorem S_le : (∑ i, (X.s i : ℝ)) ≤ X.D := by
  calc (∑ i, (X.s i : ℝ)) ≤ ∑ i, (X.D : ℝ) * X.π i := sum_le_sum fun i _ ↦ X.s_le i
    _ = X.D := by rw [← mul_sum, X.hπ.2.1, mul_one]

theorem one_le_P : (1 : ℝ) ≤ X.P := by
  have : 1 ≤ X.P := Nat.one_le_iff_ne_zero.2
    (prod_ne_zero_iff.2 fun c _ ↦ Nat.one_le_iff_ne_zero.1 (X.one_le_s c))
  exact_mod_cast this

theorem one_le_cnt : (1 : ℝ) ≤ X.cnt := by
  have : 1 ≤ X.cnt := by
    unfold cnt
    have := X.hH; have := X.hm
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  exact_mod_cast this

theorem deg_eq : ((X.design.deg a : ℕ) : ℝ) = (X.P : ℝ) ^ 2 * X.cnt * ((4 : ℝ) ^ a) ^ X.r := by
  change ((X.d₀ * (4 ^ a) ^ X.r : ℕ) : ℝ) = _
  unfold d₀
  push_cast
  ring

theorem card_Ty_real : (Fintype.card X.Ty : ℝ) = (∑ i, (X.s i : ℝ)) * X.cnt := by
  rw [card_Ty]; push_cast; ring

/-- The error of the bilinear approximation is at most `ξ / 2` times the degree. -/
theorem Eb_le {n η : ℝ} (hn : 0 ≤ n) (hη : 0 ≤ η) :
    (Fintype.card X.Ty : ℝ) * err a X.r * n + 2 * X.m * (η * n) / 2 ≤
      (X.D * 8 ^ X.r / 2 ^ a + X.m * η) * (X.design.deg a * n) := by
  rw [X.deg_eq a, X.card_Ty_real]
  set S := ∑ i, (X.s i : ℝ)
  have hS := X.S_le
  have hS0 : 0 ≤ S := sum_nonneg fun i _ ↦ Nat.cast_nonneg _
  have hP := X.one_le_P
  have hc := X.one_le_cnt
  have h4 : (1 : ℝ) ≤ ((4 : ℝ) ^ a) ^ X.r := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have he := err_mul_le a X.r
  have h2 : (0 : ℝ) < 2 ^ a := by positivity
  have herr : err a X.r ≤ 8 ^ X.r * ((4 : ℝ) ^ a) ^ X.r / 2 ^ a := by
    rw [le_div_iff₀ h2]; exact he
  have hP2 : (1 : ℝ) ≤ (X.P : ℝ) ^ 2 := one_le_pow₀ hP
  have hm : (0 : ℝ) ≤ X.m := Nat.cast_nonneg _
  have hD : (0 : ℝ) ≤ X.D := Nat.cast_nonneg _
  have e0 : (0 : ℝ) ≤ 8 ^ X.r * ((4 : ℝ) ^ a) ^ X.r / 2 ^ a := by positivity
  have t1 : S * X.cnt * err a X.r * n ≤
      X.D * X.cnt * (8 ^ X.r * ((4 : ℝ) ^ a) ^ X.r / 2 ^ a) * n := by
    have := mul_le_mul hS herr (err_nonneg a X.r) hD
    have hcn : (0 : ℝ) ≤ X.cnt * n := by positivity
    nlinarith [mul_le_mul_of_nonneg_right this hcn]
  have t2 : X.D * X.cnt * (8 ^ X.r * ((4 : ℝ) ^ a) ^ X.r / 2 ^ a) * n ≤
      X.D * 8 ^ X.r / 2 ^ a * ((X.P : ℝ) ^ 2 * X.cnt * ((4 : ℝ) ^ a) ^ X.r * n) := by
    have hx : (0 : ℝ) ≤ X.D * X.cnt * (8 ^ X.r * ((4 : ℝ) ^ a) ^ X.r / 2 ^ a) * n := by
      positivity
    have : X.D * X.cnt * (8 ^ X.r * ((4 : ℝ) ^ a) ^ X.r / 2 ^ a) * n * 1 ≤
        X.D * X.cnt * (8 ^ X.r * ((4 : ℝ) ^ a) ^ X.r / 2 ^ a) * n * (X.P : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hP2 hx
    calc _ = X.D * X.cnt * (8 ^ X.r * ((4 : ℝ) ^ a) ^ X.r / 2 ^ a) * n * 1 := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have t3 : 2 * X.m * (η * n) / 2 ≤
      X.m * η * ((X.P : ℝ) ^ 2 * X.cnt * ((4 : ℝ) ^ a) ^ X.r * n) := by
    have hx : (0 : ℝ) ≤ X.m * η * n := by positivity
    have h1 : (1 : ℝ) ≤ (X.P : ℝ) ^ 2 * X.cnt * ((4 : ℝ) ^ a) ^ X.r := by
      have := mul_le_mul hP2 hc zero_le_one (by positivity)
      have := mul_le_mul this h4 zero_le_one (by positivity)
      linarith
    have := mul_le_mul_of_nonneg_left h1 hx
    calc 2 * X.m * (η * n) / 2 = X.m * η * n * 1 := by ring
      _ ≤ _ := this
      _ = _ := by ring
  calc S * X.cnt * err a X.r * n + 2 * X.m * (η * n) / 2 ≤
      X.D * 8 ^ X.r / 2 ^ a * ((X.P : ℝ) ^ 2 * X.cnt * ((4 : ℝ) ^ a) ^ X.r * n) +
        X.m * η * ((X.P : ℝ) ^ 2 * X.cnt * ((4 : ℝ) ^ a) ^ X.r * n) :=
      add_le_add (t1.trans t2) t3
    _ = _ := by ring

/-- `κ |e| / d = V_e`. -/
theorem κ_class_div (G : Graph) (hn : 0 < G.1) (J : Finset (Fin G.1)) (b : Fin X.k) :
    X.κ * ((univ.filter fun p ↦ (X.labels a).chi J p = b).card : ℝ) /
      ((X.design.deg a * G.1 : ℕ) : ℝ) =
      (∑ j, (X.s j : ℝ) * X.ℓ j b) / (2 * X.H * X.D) := by
  rw [X.card_class a G J b, Nat.cast_mul, X.deg_eq a]
  have hn' : (0 : ℝ) < G.1 := by exact_mod_cast hn
  have hP : (0 : ℝ) < X.P := lt_of_lt_of_le one_pos X.one_le_P
  have hD : (0 : ℝ) < X.D := by
    have h := X.hD ⟨0, X.one_le_k⟩
    have := X.π_le_one ⟨0, X.one_le_k⟩
    have hk : (0 : ℝ) ≤ X.k := Nat.cast_nonneg _
    by_contra hc
    have : (X.D : ℝ) = 0 := le_antisymm (not_lt.1 hc) (Nat.cast_nonneg _)
    nlinarith
  have hH : (0 : ℝ) < X.H := by exact_mod_cast X.hH
  have hm : (0 : ℝ) < X.m := by exact_mod_cast X.hm
  unfold κ cnt
  push_cast
  have h4 : (0 : ℝ) < ((4 : ℝ) ^ a) ^ X.r := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ X.r := by positivity
  field_simp
  ring

/-! ### The model -/

theorem abs_chat_class_le {pm : ℝ} (hpm : 0 < pm) (hπ : ∀ i, pm ≤ X.π i) (G : Graph)
    (J : Finset (Fin G.1)) {c e : Fin X.k} {p q : Fin (X.design.blow a G).1}
    (hp : (X.labels a).chi J p = c) (hq : (X.labels a).chi J q = e) :
    |X.design.Chat (X.design.grp a p) (X.design.grp a q) - X.κ * (X.M c e / X.π e)| ≤
      X.κ * X.δ₀ pm := by
  have hi : X.M (X.design.grp a p) = X.M c := by rw [← X.row_chi a G J p, hp]
  have hj : X.M (X.design.grp a q) = X.M e := by rw [← X.row_chi a G J q, hq]
  rw [X.chat_eq, ← X.ratio_congr hi hj, ← mul_sub, abs_mul, abs_of_nonneg X.κ_nonneg]
  exact mul_le_mul_of_nonneg_left (X.abs_chat_sub_le hpm hπ _ _) X.κ_nonneg

theorem one_le_ℓ_self {pm : ℝ} (hπ : ∀ i, pm ≤ X.π i) (hHpm : (X.k : ℝ) + 1 ≤ 2 * X.H * pm)
    (c : Fin X.k) : (1 : ℝ) ≤ X.ℓ c c := by
  have h := X.abs_ℓ_sub_le c c
  have hρ : pm ≤ X.ρ c c := by
    unfold ρ
    rw [ite_eq_left (Alg.self_mem_rowGroup c)]
    have hP : X.Pi c ≤ 1 := by
      rw [← X.hπ.2.1]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun b _ _ ↦ (X.π_pos b).le
    have hP0 := X.Pi_pos c
    calc pm ≤ X.π c := hπ c
      _ ≤ X.π c / X.Pi c := by
        rw [le_div_iff₀ hP0]
        exact mul_le_of_le_one_right (X.π_pos c).le hP
  have hH : (0 : ℝ) ≤ X.H := Nat.cast_nonneg _
  have := (abs_le.1 h).1
  nlinarith

/-- **The model of the coloring is close to `M`.** -/
theorem abs_model_sub_le (G : Graph) (hn : 0 < G.1) {η : ℝ} (hη : 0 ≤ η)
    (hdeg : G.MaxDegreeLE η) (J : Finset (Fin G.1)) {pm : ℝ} (hpm : 0 < pm)
    (hπ : ∀ i, pm ≤ X.π i) (hHpm : (X.k : ℝ) + 1 ≤ 2 * X.H * pm) (c e : Fin X.k) :
    |X.M c e - (X.design.blow a G).model ((X.labels a).chi J) c e| ≤
      X.ξ a η * (1 + 2 * X.H * X.D) + X.δ₀ pm +
        ((X.k : ℝ) ^ 2 / X.D + X.k / (2 * X.H)) / pm := by
  classical
  set χ := (X.labels a).chi J with hχ
  have hreg := X.design.blow_isRegular a G
  rw [model_eq_bil _ hreg χ c e]
  have hΔ : ∀ v, ∑ v', ind (G.2.Adj v v') ≤ η * G.1 := fun v ↦ by
    rw [sum_ind_adj_eq_degree]; exact hdeg v
  have hn' : (0 : ℝ) < G.1 := by exact_mod_cast hn
  have h1 := X.design.bil_blow_sub_le a G (by positivity) X.sum_abs_W0 hΔ
    (fun p ↦ if χ p = c then 1 else 0) (fun q ↦ if χ q = e then 1 else 0)
  rw [dot_indicator, dot_indicator] at h1
  set cc : ℝ := ((univ.filter (χ · = c)).card : ℝ) with hcc
  set ce : ℝ := ((univ.filter (χ · = e)).card : ℝ) with hce
  set Q := ∑ p, ∑ q, (if χ p = c then (1 : ℝ) else 0) *
    X.design.Chat (X.design.grp a p) (X.design.grp a q) * (if χ q = e then (1 : ℝ) else 0)
  set R := X.M c e / X.π e
  have hsumx : ∑ p : Fin (X.design.blow a G).1, (if χ p = c then (1 : ℝ) else 0) = cc := by
    rw [sum_boole]
  have hsumy : ∑ q : Fin (X.design.blow a G).1, (if χ q = e then (1 : ℝ) else 0) = ce := by
    rw [sum_boole]
  have hprod : ∀ K : ℝ, K * cc * ce = ∑ p, ∑ q, (if χ p = c then (1 : ℝ) else 0) * K *
      (if χ q = e then (1 : ℝ) else 0) := by
    intro K
    rw [← hsumx, ← hsumy, mul_assoc, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun p _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun q _ ↦ ?_
    ring
  have h2 : |Q - X.κ * R * cc * ce| ≤ X.κ * X.δ₀ pm * cc * ce := by
    have hrw : Q - X.κ * R * cc * ce = ∑ p, ∑ q, (if χ p = c then (1 : ℝ) else 0) *
        (X.design.Chat (X.design.grp a p) (X.design.grp a q) - X.κ * R) *
          (if χ q = e then (1 : ℝ) else 0) := by
      rw [hprod, ← sum_sub_distrib]
      refine sum_congr rfl fun p _ ↦ ?_
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun q _ ↦ ?_
      ring
    have hpt : ∀ p q, |(if χ p = c then (1 : ℝ) else 0) *
        (X.design.Chat (X.design.grp a p) (X.design.grp a q) - X.κ * R) *
          (if χ q = e then (1 : ℝ) else 0)| ≤
        X.κ * X.δ₀ pm * ((if χ p = c then (1 : ℝ) else 0) * (if χ q = e then (1 : ℝ) else 0)) := by
      intro p q
      by_cases hp : χ p = c
      · by_cases hq : χ q = e
        · simp only [hp, hq, ↓reduceIte, one_mul, mul_one]
          exact X.abs_chat_class_le a hpm hπ G J hp hq
        · simp [hq]
      · simp [hp]
    rw [hrw]
    calc _ ≤ ∑ p, ∑ q, |(if χ p = c then (1 : ℝ) else 0) *
          (X.design.Chat (X.design.grp a p) (X.design.grp a q) - X.κ * R) *
            (if χ q = e then (1 : ℝ) else 0)| :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ ↦ abs_sum_le_sum_abs _ _)
      _ ≤ ∑ p, ∑ q, X.κ * X.δ₀ pm *
          ((if χ p = c then (1 : ℝ) else 0) * (if χ q = e then (1 : ℝ) else 0)) :=
          sum_le_sum fun p _ ↦ sum_le_sum fun q _ ↦ hpt p q
      _ = X.κ * X.δ₀ pm * cc * ce := by
          rw [hprod]
          refine sum_congr rfl fun p _ ↦ sum_congr rfl fun q _ ↦ ?_
          ring
  have hV := X.κ_class_div a G hn J e
  have hEb := X.Eb_le a hn'.le hη
  -- the color classes
  have hcc' := X.card_class a G J c
  have hce' := X.card_class a G J e
  set Γ : ℝ := G.1 * (2 * 4 ^ a) ^ X.r * (X.m * (X.m + 1))
  have hΓ : 0 < Γ := by have := X.hm; positivity
  have hℓc : (1 : ℝ) ≤ ∑ j, (X.s j : ℝ) * X.ℓ j c := by
    have h1' := X.one_le_ℓ_self hπ hHpm c
    have h2' : (1 : ℝ) ≤ X.s c := by exact_mod_cast X.one_le_s c
    calc (1 : ℝ) ≤ X.s c * X.ℓ c c := by nlinarith
      _ ≤ _ := single_le_sum (f := fun j ↦ (X.s j : ℝ) * X.ℓ j c)
          (fun j _ ↦ by positivity) (mem_univ c)
  have hℓe : ∑ j, (X.s j : ℝ) * X.ℓ j e ≤ 2 * X.H * X.D := by
    calc ∑ j, (X.s j : ℝ) * X.ℓ j e ≤ ∑ j, (X.s j : ℝ) * (2 * X.H) :=
          sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (X.ℓ_le j e) (Nat.cast_nonneg _)
      _ = 2 * X.H * ∑ j, (X.s j : ℝ) := by rw [← sum_mul]; ring
      _ ≤ 2 * X.H * X.D := mul_le_mul_of_nonneg_left X.S_le (by positivity)
  have hcc0 : 0 < cc := by
    rw [hcc, hcc']
    have : (0 : ℝ) < ∑ j, (X.s j : ℝ) * X.ℓ j c := lt_of_lt_of_le one_pos hℓc
    have := X.hm
    positivity
  have hratio : ce ≤ 2 * X.H * X.D * cc := by
    rw [hce, hcc, hce', hcc']
    have hx : (0 : ℝ) ≤ G.1 * (2 * 4 ^ a) ^ X.r * (X.m * (X.m + 1)) := by positivity
    calc (G.1 : ℝ) * (2 * 4 ^ a) ^ X.r * (X.m * (X.m + 1) * ∑ j, (X.s j : ℝ) * X.ℓ j e) =
          (G.1 * (2 * 4 ^ a) ^ X.r * (X.m * (X.m + 1))) * ∑ j, (X.s j : ℝ) * X.ℓ j e := by ring
      _ ≤ (G.1 * (2 * 4 ^ a) ^ X.r * (X.m * (X.m + 1))) * (2 * X.H * X.D * 1) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left hℓe hx
      _ ≤ (G.1 * (2 * 4 ^ a) ^ X.r * (X.m * (X.m + 1))) *
          (2 * X.H * X.D * ∑ j, (X.s j : ℝ) * X.ℓ j c) := by gcongr
      _ = _ := by ring
  have hdR : (0 : ℝ) < ((X.design.deg a * G.1 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, X.deg_eq a]
    have := X.one_le_P; have := X.one_le_cnt
    positivity
  have hEb' : (Fintype.card X.Ty : ℝ) * err a X.r * G.1 + 2 * X.m * (η * G.1) / 2 ≤
      (X.D * 8 ^ X.r / 2 ^ a + X.m * η) * ((X.design.deg a * G.1 : ℕ) : ℝ) := by
    rw [Nat.cast_mul]; exact hEb
  have hM : X.M c e = R * X.π e := by
    simp only [R]; field_simp [(X.π_pos e).ne']
  have hR0 : 0 ≤ R := div_nonneg (X.M_nonneg c e) (X.π_pos e).le
  have hA0 : 0 ≤ (X.D : ℝ) * 8 ^ X.r / 2 ^ a + X.m * η := by positivity
  have hδ0 : 0 ≤ X.δ₀ pm := by unfold δ₀; positivity
  have key := abs_model_arith (πe := X.π e) hcc0 hdR (Nat.cast_nonneg _) X.κ_nonneg hδ0 hR0 hA0
    h1 h2 hV hEb' hratio (X.V_le_one e)
  rw [hM]
  refine key.trans ?_
  -- the final comparison
  have hξ : (X.D : ℝ) * 8 ^ X.r / 2 ^ a + X.m * η ≤ X.ξ a η := by
    unfold ξ
    have : (0 : ℝ) ≤ X.D * 8 ^ X.r / 2 ^ a := by positivity
    have : (0 : ℝ) ≤ X.m * η := by positivity
    have e1 : (2 : ℝ) * X.D * 8 ^ X.r / 2 ^ a = 2 * (X.D * 8 ^ X.r / 2 ^ a) := by ring
    linarith
  have hT : (0 : ℝ) ≤ 1 + 2 * X.H * X.D := by positivity
  have hRle : R ≤ 1 / pm := by
    simp only [R]
    rw [div_le_div_iff₀ (X.π_pos e) hpm]
    calc X.M c e * pm ≤ 1 * pm := mul_le_mul_of_nonneg_right (X.M_le_one c e) hpm.le
      _ ≤ 1 * X.π e := by rw [one_mul, one_mul]; exact hπ e
  have hVe := X.abs_V_sub_le e
  have h3 : R * |(∑ j, (X.s j : ℝ) * X.ℓ j e) / (2 * X.H * X.D) - X.π e| ≤
      ((X.k : ℝ) ^ 2 / X.D + X.k / (2 * X.H)) / pm := by
    rw [div_eq_mul_one_div _ pm, mul_comm _ (1 / pm)]
    exact mul_le_mul hRle hVe (abs_nonneg _) (by positivity)
  have h4 := mul_le_mul_of_nonneg_right hξ hT
  linarith

/-! ### The cover -/

/-- **The monochromatic edges are covered by few vertices.** -/
theorem card_cover_le (G : Graph) {I J : Finset (Fin G.1)} (hIJ : Disjoint I J) {εB : ℝ}
    (hIc : (1 / 2 - εB) * G.1 ≤ I.card) (hJc : (1 / 2 - εB) * G.1 ≤ J.card) :
    (((X.labels a).cover J I).card : ℝ) ≤
      (1 / (X.m + 1) + 2 * εB) * (X.design.blow a G).1 := by
  have h := (X.labels a).card_cover_le J I
  rw [LowRank.card_outside hIJ] at h
  have hg : ((univ.filter (X.labels a).garbage).card : ℝ) =
      (2 * 4 ^ a) ^ X.r * (univ.filter X.absb).card := by
    exact_mod_cast X.design.card_cells a X.absb
  have hW : ((univ.filter fun u ↦ (X.design.template a).W u u = 1).card : ℝ) ≤
      Fintype.card (X.design.Cell a) := by
    exact_mod_cast (card_filter_le _ _).trans (by simp)
  have hN : ((X.design.blow a G).1 : ℝ) = Fintype.card (X.design.Cell a) * G.1 := by
    push_cast; rfl
  have hcell : (Fintype.card (X.design.Cell a) : ℝ) = Fintype.card X.Ty * (2 * 4 ^ a) ^ X.r := by
    exact_mod_cast X.design.card_cell a
  have habs := X.card_absb_le
  have hm : (0 : ℝ) < X.m + 1 := by positivity
  have hn : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
  have hout0 : (0 : ℝ) ≤ G.1 - I.card - J.card := by
    rw [← LowRank.card_outside hIJ]; positivity
  have hout : (G.1 : ℝ) - I.card - J.card ≤ 2 * εB * G.1 := by linarith
  rw [hg] at h
  rw [hN, hcell]
  rw [hcell] at hW
  set Γ : ℝ := (2 * 4 ^ a) ^ X.r
  have hΓ : 0 < Γ := by positivity
  have h1 : Γ * (univ.filter X.absb).card * G.1 ≤
      1 / (X.m + 1) * (Fintype.card X.Ty * Γ * G.1) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm]
    have := mul_le_mul_of_nonneg_left habs (mul_nonneg hΓ.le hn)
    nlinarith
  have h2 := mul_le_mul hW hout hout0 (by positivity)
  nlinarith

/-! ### The spectrum -/

theorem κ_card_cells_le : X.κ * Fintype.card (X.design.Cell a) ≤ X.design.deg a := by
  rw [X.card_cells a, X.deg_eq a]
  unfold κ
  have hD : (0 : ℝ) < X.D := by
    have h := X.hD ⟨0, X.one_le_k⟩
    have := X.π_le_one ⟨0, X.one_le_k⟩
    have hk : (0 : ℝ) ≤ X.k := Nat.cast_nonneg _
    by_contra hc
    have : (X.D : ℝ) = 0 := le_antisymm (not_lt.1 hc) (Nat.cast_nonneg _)
    nlinarith
  have hS := X.S_le
  have h2 : (0 : ℝ) < 2 ^ X.r := by positivity
  rw [mul_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hx : (0 : ℝ) ≤ (X.P : ℝ) ^ 2 * X.cnt * ((4 : ℝ) ^ a) ^ X.r * 2 ^ X.r := by positivity
  have := mul_le_mul_of_nonneg_left hS hx
  nlinarith

theorem thr_le {n η pm : ℝ} (hn : 0 < n) (hη : 0 ≤ η) (hpm : 0 < pm) :
    (2 * ((Fintype.card X.Ty : ℝ) * err a X.r * n + 2 * X.m * (η * n) / 2) +
      X.κ * X.δ₀ pm * ((Fintype.card (X.design.Cell a) : ℝ) * n)) / (X.design.deg a * n) ≤
      X.ξ a η + X.δ₀ pm := by
  have hd : (0 : ℝ) < X.design.deg a := by
    rw [X.deg_eq a]
    have := X.one_le_P; have := X.one_le_cnt
    positivity
  have hE := X.Eb_le a hn.le hη
  have hc := X.κ_card_cells_le a
  have hδ0 : 0 ≤ X.δ₀ pm := by unfold δ₀; positivity
  rw [div_le_iff₀ (by positivity)]
  have h1 : X.κ * X.δ₀ pm * ((Fintype.card (X.design.Cell a) : ℝ) * n) ≤
      X.δ₀ pm * (X.design.deg a * n) := by
    have := mul_le_mul_of_nonneg_left hc (mul_nonneg hδ0 hn.le)
    nlinarith
  have h2 : X.ξ a η = 2 * (X.D * 8 ^ X.r / 2 ^ a + X.m * η) := by unfold ξ; ring
  rw [h2]
  nlinarith

/-- **The blow-up is a one-sided expander.** -/
theorem isOneSidedExpander (G : Graph) (hn : 0 < G.1) {η : ℝ} (hη : 0 ≤ η)
    (hdeg : G.MaxDegreeLE η) {pm lam : ℝ} (hpm : 0 < pm) (hπ : ∀ i, pm ≤ X.π i)
    (hlam : X.ξ a η + X.δ₀ pm ≤ lam) :
    (X.design.blow a G).IsOneSidedExpander lam := by
  classical
  have hΔ : ∀ v, ∑ v', ind (G.2.Adj v v') ≤ η * G.1 := fun v ↦ by
    rw [sum_ind_adj_eq_degree]; exact hdeg v
  have hn' : (0 : ℝ) < G.1 := by exact_mod_cast hn
  have hd : 0 < X.design.deg a := by
    have : (0 : ℝ) < X.design.deg a := by
      rw [X.deg_eq a]
      have := X.one_le_P; have := X.one_le_cnt
      positivity
    exact_mod_cast this
  have hδ0 : 0 ≤ X.δ₀ pm := by unfold δ₀; positivity
  have h := X.design.numEigGT_blow_le a G hn hd (by positivity) X.sum_abs_W0 hΔ
    (fun i j ↦ X.κ * (X.M i j / X.π j)) (mul_nonneg X.κ_nonneg hδ0) (fun i j ↦ ?_)
    (L := 1) (fun _ _ ↦ (1 : ℝ)) (fun Y hY ↦ ?_)
  · unfold Graph.IsOneSidedExpander
    refine le_trans (LowRank.numEigGT_anti _ ?_) h
    exact (X.thr_le a hn' hη hpm).trans hlam
  · rw [X.chat_eq, ← mul_sub, abs_mul, abs_of_nonneg X.κ_nonneg]
    exact mul_le_mul_of_nonneg_left (X.abs_chat_sub_le hpm hπ _ _) X.κ_nonneg
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

/-! ### Yes-instances -/

/-- **Yes-instances**: the blow-up is a regular `λ`-one-sided expander with an
`(M, ε)`-coloring. -/
theorem yes (G : Graph) (hn : 0 < G.1) {εB η ε lam pm : ℝ} (hη : 0 ≤ η) (hpm : 0 < pm)
    (hπ : ∀ i, pm ≤ X.π i) (hHpm : (X.k : ℝ) + 1 ≤ 2 * X.H * pm) (hdeg : G.MaxDegreeLE η)
    {I J : Finset (Fin G.1)} (hIJ : Disjoint I J) (hI : G.2.IsIndepSet (I : Set (Fin G.1)))
    (hJ : G.2.IsIndepSet (J : Set (Fin G.1))) (hIc : (1 / 2 - εB) * G.1 ≤ I.card)
    (hJc : (1 / 2 - εB) * G.1 ≤ J.card) (hcov : 1 / (X.m + 1) + 2 * εB ≤ ε)
    (hmod : X.ξ a η * (1 + 2 * X.H * X.D) + X.δ₀ pm +
      ((X.k : ℝ) ^ 2 / X.D + X.k / (2 * X.H)) / pm ≤ ε)
    (hlam : X.ξ a η + X.δ₀ pm ≤ lam) :
    (X.design.blow a G).IsRegular ∧ (X.design.blow a G).IsOneSidedExpander lam ∧
      (X.design.blow a G).MColorable X.M ε := by
  classical
  refine ⟨⟨_, X.design.blow_isRegular a G⟩, X.isOneSidedExpander a G hn hη hdeg hpm hπ hlam,
    (X.labels a).chi J, fun c e ↦ (X.abs_model_sub_le a G hn hη hdeg J hpm hπ hHpm c e).trans hmod,
    (X.labels a).cover J I, ?_, fun p q hpq hχ ↦ (X.labels a).mono_cover J (X.labels_valid a) hI hJ
      hpq hχ⟩
  have h := X.card_cover_le a G hIJ hIc hJc
  have hN : (0 : ℝ) ≤ (X.design.blow a G).1 := Nat.cast_nonneg _
  exact h.trans (mul_le_mul_of_nonneg_right hcov hN)

end Data

end ModelRed

end BHSV25.Hard
