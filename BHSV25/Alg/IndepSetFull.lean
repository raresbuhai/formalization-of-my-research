module

public import BHSV25.Alg.IndepSetGS
public import BHSV25.Spectral.ThresholdRank
public import BHSV25.Time

/-!
# Theorem 7.20 and Corollary 7.21 (Theorem 1.1)

[BHSV25, Theorem 7.20] (`BHSV25.Alg.indepSet_bottomRank`): for every `c > 0`,
`λ ∈ (0, 1)`, `t` and `γ ∈ (0, 1/4)`, an algorithm running in time
`(D (1 + (1 - λ) / γ))^(D (t + 1)) · m^C`, with `C` independent of all parameters and `D`
depending only on `c`, that outputs an independent set of at least
`(1/2 - γ - (4 + c) γ / (1 - λ)) n` vertices on regular graphs with at most `t` eigenvalues at most
`-λ` and an independent set of `(1/2 - γ) n` vertices. Corollary 7.21
(`BHSV25.Alg.indepSet_topRank`) follows from Corollary 4.2: at most `t` eigenvalues
above `λ < 1/2` leave at most `t / λ²` at most `-√(2λ)`.

**The parameters** of `BHSV25.Alg.indepAlgGS`, for `c₁ = min(c, 1)` and `c'' = η = c₁/32`:
`K = ⌈A (1 + (1 - λ)/γ)⌉` with `A = 32 (1 + 32/c₁) / c + 1`, so that the precision `ρ = 4/K`
costs `(1 + 1/η) ρ² ≤ (c/2) γ / (1 - λ)`; the radius `N = (⌊√t⌋ + 1) K` and the budget
`B = (3 + 12 K)^t` of the grid; the power `a n⁵` of the filter with `a = ⌈8 (t + 2 + K/2) / c''⌉`.
The machine reads them in unary, so its running time is `c₀ (|p| + 1)^C₀ · m^C₀`
(`BHSV25.runsInTime_graph_fix`), and `|p| + 1 ≤ (768/c₁ + 11) (15 K)^(t + 1)`
(`BHSV25.Alg.length_params_le`).
-/

@[expose] public section

namespace BHSV25.Alg

open Turing.MultiTapeTM

/-! ### The size of the parameters -/

theorem length_encGSPar (p : ℕ × ℕ × ℕ × ℕ) :
    (Net.encGSPar p).length = 2 * p.1 + 2 * p.2.1 + 2 * p.2.2.1 + p.2.2.2 + 3 := by
  simp [encUnary_apply]
  ring

theorem add_two_le_two_pow (t : ℕ) : (t : ℝ) + 2 ≤ 2 ^ (t + 1) := by
  have h : t + 2 ≤ 2 ^ (t + 1) := by
    induction t with
    | zero => norm_num
    | succ t ih => rw [pow_succ]; omega
  exact_mod_cast h

/-- **The size of the parameters**: `|p| + 1 ≤ (768/c₁ + 11) (15 K)^(t + 1)`. -/
theorem length_params_le {c₁ : ℝ} (hc₁ : 0 < c₁) (hc1 : c₁ ≤ 1) {t K a : ℕ} (hK : 1 ≤ K)
    (ha : (a : ℝ) ≤ 256 / c₁ * (t + 2 + K / 2) + 1) :
    ((Net.encGSPar (a, t, (Nat.sqrt t + 1) * K, (3 + 12 * K) ^ t)).length + 1 : ℝ) ≤
      (768 / c₁ + 11) * (15 * K) ^ (t + 1) := by
  rw [length_encGSPar]
  simp only
  push_cast
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set Z : ℝ := (15 * K) ^ (t + 1) with hZ
  have hZ1 : 1 ≤ Z := one_le_pow₀ (by linarith)
  -- `(t + 2) K ≤ Z`
  have hx : ((t : ℝ) + 2) * K ≤ Z := by
    have h1 := add_two_le_two_pow t
    calc ((t : ℝ) + 2) * K ≤ 2 ^ (t + 1) * (K : ℝ) ^ (t + 1) :=
          mul_le_mul h1 (le_self_pow₀ hK' (by omega)) (by linarith) (by positivity)
      _ = (2 * K) ^ (t + 1) := by rw [mul_pow]
      _ ≤ Z := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hc₁' : 1 ≤ 1 / c₁ := by rw [le_div_iff₀ hc₁]; linarith
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hxK : (K : ℝ) ≤ ((t : ℝ) + 2) * K := by nlinarith
  have hxt : (t : ℝ) + 2 ≤ ((t : ℝ) + 2) * K := by nlinarith
  -- `a ≤ (384/c₁ + 1) Z`
  have ha' : (a : ℝ) ≤ (384 / c₁ + 1) * Z := by
    have e : 256 / c₁ * (t + 2 + K / 2 : ℝ) + 1 =
        256 * (1 / c₁) * (t + 2) + 128 * (1 / c₁) * K + 1 := by ring
    have h1 : 256 * (1 / c₁) * ((t : ℝ) + 2) ≤ 256 * (1 / c₁) * (((t : ℝ) + 2) * K) :=
      mul_le_mul_of_nonneg_left hxt (by positivity)
    have h2 : 128 * (1 / c₁) * (K : ℝ) ≤ 128 * (1 / c₁) * (((t : ℝ) + 2) * K) :=
      mul_le_mul_of_nonneg_left hxK (by positivity)
    have h3 : (1 : ℝ) ≤ ((t : ℝ) + 2) * K := by nlinarith
    have e2 : (384 / c₁ + 1) * Z = 384 * (1 / c₁) * Z + Z := by ring
    rw [e2]
    have h4 := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ 384 * (1 / c₁))
    linarith
  -- the other parameters
  have hN : (((Nat.sqrt t : ℕ) : ℝ) + 1) * K ≤ Z := by
    have : ((Nat.sqrt t : ℕ) : ℝ) ≤ t := by exact_mod_cast Nat.sqrt_le_self t
    nlinarith
  have hB : ((3 : ℝ) + 12 * K) ^ t ≤ Z := by
    calc ((3 : ℝ) + 12 * K) ^ t ≤ (15 * K) ^ t := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ Z := pow_le_pow_right₀ (by linarith) (by omega)
  have ht : (t : ℝ) ≤ Z := by linarith
  have e1 : (384 / c₁ + 1) * Z = 384 * (Z / c₁) + Z := by ring
  have e2 : (768 / c₁ + 11) * Z = 768 * (Z / c₁) + 11 * Z := by ring
  rw [e1] at ha'
  rw [e2]
  linarith

/-- **The factor**: if `|p| + 1 ≤ M (15 K)^(t + 1)` and `K ≤ 2 A W` with `A, W ≥ 1`, then
`c₀ (|p| + 1)^C₀ ≤ (D W)^(D (t + 1))` for `D = ⌈max(1, c₀ M^C₀) · 30 A⌉ + C₀ + 1`. -/
theorem factor_le (c₀ C₀ : ℕ) {M A W : ℝ} (hA : 1 ≤ A) (hW : 1 ≤ W) {t K : ℕ}
    (hK : (K : ℝ) ≤ 2 * A * W) {L : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ M * (15 * K) ^ (t + 1)) :
    (c₀ : ℝ) * L ^ C₀ ≤
      (((⌈max 1 (c₀ * M ^ C₀) * 30 * A⌉₊ + C₀ + 1 : ℕ) : ℝ) * W) ^
        ((⌈max 1 (c₀ * M ^ C₀) * 30 * A⌉₊ + C₀ + 1) * (t + 1)) := by
  set Y := max 1 ((c₀ : ℝ) * M ^ C₀) with hY
  set D := ⌈Y * 30 * A⌉₊ + C₀ + 1 with hD
  have hY1 : 1 ≤ Y := le_max_left _ _
  have hZ : (15 : ℝ) * K ≤ 30 * A * W := by linarith
  have hZ0 : (0 : ℝ) ≤ 15 * K := by positivity
  have h30 : (1 : ℝ) ≤ 30 * A * W := by nlinarith
  have hDY : Y * 30 * A ≤ D := by
    rw [hD]
    push_cast
    have := Nat.le_ceil (Y * 30 * A)
    linarith
  have hDW1 : (1 : ℝ) ≤ D * W := by
    have : (1 : ℝ) ≤ D := by rw [hD]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈Y * 30 * A⌉₊]
    nlinarith
  set m := C₀ + 1 with hm
  -- `c₀ L^C₀ ≤ Y (30 A W)^(C₀ (t + 1))`
  have h1 : (c₀ : ℝ) * L ^ C₀ ≤ Y * (30 * A * W) ^ (C₀ * (t + 1)) := by
    calc (c₀ : ℝ) * L ^ C₀ ≤ c₀ * (M * (15 * K) ^ (t + 1)) ^ C₀ :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hL _) (Nat.cast_nonneg _)
      _ = (c₀ * M ^ C₀) * ((15 * K) ^ (t + 1)) ^ C₀ := by rw [mul_pow]; ring
      _ ≤ Y * ((15 * K) ^ (t + 1)) ^ C₀ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = Y * (15 * K) ^ (C₀ * (t + 1)) := by rw [← pow_mul, mul_comm (t + 1)]
      _ ≤ Y * (30 * A * W) ^ (C₀ * (t + 1)) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hZ0 hZ _) (by linarith)
  -- `≤ (Y · 30 A W)^(m (t + 1))`
  have h2 : Y * (30 * A * W) ^ (C₀ * (t + 1)) ≤ (Y * (30 * A * W)) ^ (m * (t + 1)) := by
    rw [mul_pow Y (30 * A * W)]
    have hm1 : 1 ≤ m * (t + 1) := by rw [hm]; nlinarith
    exact mul_le_mul (le_self_pow₀ hY1 (Nat.one_le_iff_ne_zero.1 hm1))
      (pow_le_pow_right₀ h30 (Nat.mul_le_mul_right _ (by omega)))
      (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
  -- `≤ (D W)^(D (t + 1))`
  have h3 : (Y * (30 * A * W)) ^ (m * (t + 1)) ≤ ((D : ℝ) * W) ^ (D * (t + 1)) := by
    have e : Y * (30 * A * W) = (Y * 30 * A) * W := by ring
    rw [e]
    calc ((Y * 30 * A) * W) ^ (m * (t + 1)) ≤ ((D : ℝ) * W) ^ (m * (t + 1)) :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hDY (by linarith)) _
      _ ≤ ((D : ℝ) * W) ^ (D * (t + 1)) :=
          pow_le_pow_right₀ hDW1 (Nat.mul_le_mul_right _ (by rw [hm, hD]; omega))
  exact h1.trans (h2.trans h3)

/-! ### The arithmetic of the guarantee -/

/-- The coefficient of the loss: `(1 + c'') 4 / ((1 - c'') (1 - λ)) ≤ (4 + c/2) / (1 - λ)` for
`c'' = c₁ / 32`, `c₁ ≤ min(c, 1)`. -/
theorem coef_loss_le {c c₁ cc lam : ℝ} (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1) (hc₁c : c₁ ≤ c)
    (hcc : cc = c₁ / 32) (hl1 : lam < 1) :
    (1 + cc) * 4 / ((1 - cc) * (1 - lam)) ≤ (4 + c / 2) / (1 - lam) := by
  have hl' : 0 < 1 - lam := by linarith
  have hcc1 : cc < 1 := by rw [hcc]; linarith
  rw [div_le_div_iff₀ (mul_pos (by linarith) hl') hl']
  have h1 : (1 + cc) * 4 ≤ (4 + c / 2) * (1 - cc) := by
    rw [hcc]
    nlinarith
  nlinarith

/-- The cost of the precision: `(1 + 1/c'') (4/K)² ≤ (c/2) γ / (1 - λ)` for
`K ≥ (32 (1 + 32/c₁) / c + 1) (1 + (1 - λ)/γ)`. -/
theorem coef_prec_le {c c₁ cc lam γ A₁ W : ℝ} {K : ℕ} (hc : 0 < c) (hc₁0 : 0 < c₁)
    (hcc : cc = c₁ / 32) (hl1 : lam < 1) (hγ0 : 0 < γ) (hA₁ : A₁ = 32 * (1 + 32 / c₁) / c + 1)
    (hW : W = 1 + (1 - lam) / γ) (hKge : A₁ * W ≤ K) :
    (1 + 1 / cc) * (4 / K) ^ 2 ≤ c / 2 * γ / (1 - lam) := by
  have hl' : 0 < 1 - lam := by linarith
  set X := 32 * (1 + 32 / c₁) / c with hX
  set Q := (1 - lam) / γ with hQ
  have hX0 : 0 ≤ X := by positivity
  have hQ0 : 0 ≤ Q := div_nonneg hl'.le hγ0.le
  have hK1 : (1 : ℝ) ≤ K := by
    have : (1 : ℝ) ≤ A₁ * W := by rw [hA₁, hW]; nlinarith
    linarith
  have hK2 : X * Q ≤ (K : ℝ) ^ 2 := by
    have : X * Q ≤ A₁ * W := by rw [hA₁, hW]; nlinarith
    nlinarith
  have e : (1 + 1 / cc) * (4 / K) ^ 2 = (c / 2 * γ / (1 - lam)) * (X * Q) / (K : ℝ) ^ 2 := by
    rw [hcc, hX, hQ]
    field_simp
    ring
  rw [e, div_le_iff₀ (by positivity)]
  exact mul_le_mul_of_nonneg_left hK2 (by positivity)

/-- The final count: `|I| - X g - B n ≤ out` with `0 ≤ g = n/2 - |I| ≤ γ n`,
`X ≤ (4 + c/2) / (1 - λ)` and `B ≤ (c/2) γ / (1 - λ)` give
`(1/2 - γ - (4 + c) γ / (1 - λ)) n ≤ out`. -/
theorem final_count_le {c lam γ n Ic out X Bρ : ℝ} (hl1 : lam < 1) (hc : 0 < c) (hn : 0 ≤ n)
    (hg0 : 0 ≤ n / 2 - Ic) (hgγ : n / 2 - Ic ≤ γ * n)
    (hX : X ≤ (4 + c / 2) / (1 - lam)) (hB : Bρ ≤ c / 2 * γ / (1 - lam))
    (hmain : Ic - X * (n / 2 - Ic) - Bρ * n ≤ out) :
    (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * n ≤ out := by
  have hl' : 0 < 1 - lam := by linarith
  have h1 := mul_le_mul_of_nonneg_right hX hg0
  have h2 := mul_le_mul_of_nonneg_left hgγ (by positivity : (0 : ℝ) ≤ (4 + c / 2) / (1 - lam))
  have h3 := mul_le_mul_of_nonneg_right hB hn
  have e : (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * n =
      n / 2 - γ * n - (4 + c / 2) / (1 - lam) * (γ * n) - c / 2 * γ / (1 - lam) * n := by
    field_simp
    ring
  rw [e]
  linarith

open Classical in
/-- **The guarantee for the chosen parameters.** -/
theorem card_indepAlgGS_final (G : Graph) (hreg : G.IsRegular) {lam : ℝ} (hl0 : 0 < lam)
    (hl1 : lam < 1) {t : ℕ} (ht : (Finset.univ.filter fun i ↦ G.eig i ≤ -lam).card ≤ t)
    {c c₁ cc γ A₁ W : ℝ} (hc : 0 < c) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1) (hc₁c : c₁ ≤ c)
    (hcc : cc = c₁ / 32) (hγ0 : 0 < γ) (hA₁ : A₁ = 32 * (1 + 32 / c₁) / c + 1)
    (hW : W = 1 + (1 - lam) / γ) {K a : ℕ} (hKpos : 0 < K) (hKge : A₁ * W ≤ K)
    (hage : 8 / cc * (t + 2 + K / 2 : ℝ) ≤ a) (hInd : G.HasIndepSet ((1 / 2 - γ) * G.1)) :
    (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * G.1 ≤
      (G.vertexSet (indepAlgGS (a, t, (Nat.sqrt t + 1) * K, (3 + 12 * K) ^ t)
        (G.1, adjTable G))).card := by
  obtain ⟨I, hI, hIcard⟩ := hInd
  obtain ⟨d, hd⟩ := hreg
  have hl' : 0 < 1 - lam := by linarith
  have hcc0 : 0 < cc := by rw [hcc]; positivity
  have hcc1 : cc < 1 := by rw [hcc]; linarith
  rcases Nat.eq_zero_or_pos G.1 with hn0 | hn
  · have : (G.1 : ℝ) = 0 := by exact_mod_cast hn0
    rw [this, mul_zero]
    exact Nat.cast_nonneg _
  by_cases hd0 : d = 0
  · -- no edges: all vertices
    subst hd0
    have h := card_indepAlg_of_degree_zero (indepNet (a, t, (Nat.sqrt t + 1) * K,
      (3 + 12 * K) ^ t)) G hd
    have h' : (G.1 : ℝ) ≤ (G.vertexSet (indepAlgGS (a, t, (Nat.sqrt t + 1) * K,
        (3 + 12 * K) ^ t) (G.1, adjTable G))).card := by exact_mod_cast h
    have hn' : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
    have hloss0 : 0 ≤ (4 + c) * γ / (1 - lam) := by positivity
    have : (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * G.1 ≤ G.1 := by nlinarith
    linarith
  have hmain := card_indepAlgGS_ge G hd hd0 hn hl0 hl1 ht hcc0 hcc1 hKpos hage hI hcc0
  have hg0 : 0 ≤ (G.1 : ℝ) / 2 - I.card := by
    have : (2 * I.card : ℝ) ≤ G.1 := by exact_mod_cast two_mul_card_le G hd hd0 hI
    linarith
  exact final_count_le hl1 hc (Nat.cast_nonneg _) hg0 (by linarith)
    (coef_loss_le hc₁0 hc₁1 hc₁c hcc hl1) (coef_prec_le hc hc₁0 hcc hl1 hγ0 hA₁ hW hKge) hmain

/-! ### Theorem 7.20 -/

open Classical in
/-- **Theorem 7.20** of [BHSV25]: for every `c > 0`, `λ ∈ (0, 1)`, `t` and `γ ∈ (0, 1/4)`, an
algorithm running in time `poly(n) · (γ / (1 - λ))^{-O(t)}` that, on regular graphs with at most
`t` eigenvalues at most `-λ` and an independent set of `(1/2 - γ) n` vertices, outputs an
independent set of at least `(1/2 - γ - (4 + c) γ / (1 - λ)) n` vertices. -/
theorem indepSet_bottomRank :
    ∃ C : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℕ, ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ t : ℕ,
      ∀ γ : ℝ, 0 < γ → γ < 1 / 4 →
        ∃ A : Graph → List Bool,
          RunsInTime A encGraph Encoding.encBits
            (((D : ℝ) * (1 + (1 - lam) / γ)) ^ (D * (t + 1))) C ∧
          ∀ G : Graph, G.IsRegular → (Finset.univ.filter fun i ↦ G.eig i ≤ -lam).card ≤ t →
            G.2.IsIndepSet (G.vertexSet (A G) : Set (Fin G.1)) ∧
            (G.HasIndepSet ((1 / 2 - γ) * G.1) →
              (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * G.1 ≤ (G.vertexSet (A G)).card) := by
  obtain ⟨c₀, C₀, hrun⟩ := runsInTime_graph_fix
    (V := fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ indepAlgGS z.1 z.2) indepAlgGS_polytime
  refine ⟨C₀, fun c hc ↦ ?_⟩
  -- the constants depending on `c`
  obtain ⟨c₁, hc₁⟩ : ∃ x : ℝ, x = min c 1 := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := hc₁ ▸ lt_min hc one_pos
  have hc₁1 : c₁ ≤ 1 := hc₁ ▸ min_le_right _ _
  have hc₁c : c₁ ≤ c := hc₁ ▸ min_le_left _ _
  obtain ⟨cc, hcc⟩ : ∃ x : ℝ, x = c₁ / 32 := ⟨_, rfl⟩
  have hcc0 : 0 < cc := by rw [hcc]; positivity
  obtain ⟨A₁, hA₁⟩ : ∃ x : ℝ, x = 32 * (1 + 32 / c₁) / c + 1 := ⟨_, rfl⟩
  have hA₁1 : 1 ≤ A₁ := by
    have : 0 ≤ 32 * (1 + 32 / c₁) / c := by positivity
    rw [hA₁]
    linarith
  obtain ⟨M, hM⟩ : ∃ x : ℝ, x = 768 / c₁ + 11 := ⟨_, rfl⟩
  refine ⟨⌈max 1 (c₀ * M ^ C₀) * 30 * A₁⌉₊ + C₀ + 1, fun lam hl0 hl1 t γ hγ0 hγ1 ↦ ?_⟩
  -- the parameters
  obtain ⟨W, hW⟩ : ∃ x : ℝ, x = 1 + (1 - lam) / γ := ⟨_, rfl⟩
  rw [← hW]
  have hW1 : 1 ≤ W := by
    rw [hW]
    have : 0 ≤ (1 - lam) / γ := div_nonneg (by linarith) hγ0.le
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈A₁ * W⌉₊ := ⟨_, rfl⟩
  have hKge : A₁ * W ≤ K := hK ▸ Nat.le_ceil _
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ K := le_trans (by nlinarith) hKge
    exact_mod_cast this
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = ⌈8 / cc * (t + 2 + K / 2 : ℝ)⌉₊ := ⟨_, rfl⟩
  have hage : 8 / cc * (t + 2 + K / 2 : ℝ) ≤ a := ha ▸ Nat.le_ceil _
  refine ⟨fun G ↦ indepAlgGS (a, t, (Nat.sqrt t + 1) * K, (3 + 12 * K) ^ t) (G.1, adjTable G),
    ?_, fun G hreg ht ↦ ⟨isIndepSet_indepAlg _ G, card_indepAlgGS_final G hreg hl0 hl1 ht hc
      hc₁0 hc₁1 hc₁c hcc hγ0 hA₁ hW hK1 hKge hage⟩⟩
  -- the running time
  have h := hrun (a, t, (Nat.sqrt t + 1) * K, (3 + 12 * K) ^ t)
  refine h.mono ?_ (by positivity) le_rfl
  have hale : (a : ℝ) ≤ 256 / c₁ * (t + 2 + K / 2) + 1 := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 8 / cc * (t + 2 + K / 2 : ℝ))
    have e : 8 / cc = 256 / c₁ := by rw [hcc]; field_simp; norm_num
    rw [← ha, e] at this
    linarith
  have hL := hM ▸ length_params_le hc₁0 hc₁1 hK1 hale
  have hKle : (K : ℝ) ≤ 2 * A₁ * W := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ A₁ * W)
    rw [← hK] at this
    nlinarith
  exact factor_le c₀ C₀ hA₁1 hW1 hKle (by positivity) hL

/-! ### Corollary 7.21 -/

/-- At most `t` eigenvalues above `λ < 1/2` leave at most `t / λ²` eigenvalues at most `-√(2λ)`
(Corollary 4.2, through Theorem 4.1 with `τ = √(2λ)` and `τ' = λ + λ²/2`). -/
theorem card_eig_le_neg_sqrt_le (G : Graph) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1 / 2)
    {t : ℕ} (ht : G.numEigGT lam ≤ t) :
    (Finset.univ.filter fun i ↦ G.eig i ≤ -Real.sqrt (2 * lam)).card ≤ ⌈(t : ℝ) / lam ^ 2⌉₊ := by
  set τ := Real.sqrt (2 * lam) with hτ
  have hτ0 : 0 < τ := Real.sqrt_pos.2 (by linarith)
  have hτ2 : τ ^ 2 = 2 * lam := Real.sq_sqrt (by linarith)
  set τ' := lam + lam ^ 2 / 2 with hτ'
  have hτ'lt : τ' < τ ^ 2 := by rw [hτ2, hτ']; nlinarith
  have h := Spectral.thresholdRank_graph G τ τ' hτ0 hτ'lt
  have hcount : (Finset.univ.filter fun i ↦ τ' ≤ G.eig i).card ≤ t := by
    refine le_trans (Finset.card_le_card fun i hi ↦ ?_) ht
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, lt_of_lt_of_le ?_ hi.2⟩
    rw [hτ']
    nlinarith
  have hσ : lam ≤ (τ ^ 2 - τ') / (1 - τ') := by
    have h1 : 0 < 1 - τ' := by rw [hτ']; nlinarith
    rw [le_div_iff₀ h1, hτ2, hτ']
    nlinarith
  have hσ0 : 0 ≤ lam := hl0.le
  have h2 : lam ^ 2 * ((Finset.univ.filter fun i ↦ G.eig i ≤ -τ).card : ℝ) ≤ t := by
    have h3 : lam ^ 2 ≤ ((τ ^ 2 - τ') / (1 - τ')) ^ 2 := pow_le_pow_left₀ hσ0 hσ 2
    have h4 : ((Finset.univ.filter fun i ↦ τ' ≤ G.eig i).card : ℝ) ≤ t := by
      exact_mod_cast hcount
    have h5 := mul_le_mul_of_nonneg_right h3
      (Nat.cast_nonneg (α := ℝ) (Finset.univ.filter fun i ↦ G.eig i ≤ -τ).card)
    linarith
  have h6 : ((Finset.univ.filter fun i ↦ G.eig i ≤ -τ).card : ℝ) ≤ t / lam ^ 2 := by
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact h2
  exact_mod_cast h6.trans (Nat.le_ceil _)

/-- **Theorem 1.1** of [BHSV25], full version (Corollary 7.21): for every `c > 0`,
`λ ∈ (0, 1/2)`, `t` and `γ ∈ (0, 1/4)`, an algorithm running in time
`poly(n) · (γ / (1 - √(2λ)))^{-O(t/λ²)}` that, on regular graphs with at most `t` eigenvalues
larger than `λ` and an independent set of `(1/2 - γ) n` vertices, outputs an independent set of at
least `(1/2 - γ - (4 + c) γ / (1 - √(2λ))) n` vertices. -/
theorem indepSet_topRank :
    ∃ C : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℕ, ∀ lam : ℝ, 0 < lam → lam < 1 / 2 → ∀ t : ℕ,
      ∀ γ : ℝ, 0 < γ → γ < 1 / 4 →
        ∃ A : Graph → List Bool,
          RunsInTime A encGraph Encoding.encBits
            (((D : ℝ) * (1 + (1 - Real.sqrt (2 * lam)) / γ)) ^
              (D * (⌈(t : ℝ) / lam ^ 2⌉₊ + 1))) C ∧
          ∀ G : Graph, G.IsRegular → G.numEigGT lam ≤ t →
            G.2.IsIndepSet (G.vertexSet (A G) : Set (Fin G.1)) ∧
            (G.HasIndepSet ((1 / 2 - γ) * G.1) →
              (1 / 2 - γ - (4 + c) * γ / (1 - Real.sqrt (2 * lam))) * G.1 ≤
                (G.vertexSet (A G)).card) := by
  obtain ⟨C, hC⟩ := indepSet_bottomRank
  refine ⟨C, fun c hc ↦ ?_⟩
  obtain ⟨D, hD⟩ := hC c hc
  refine ⟨D, fun lam hl0 hl1 t γ hγ0 hγ1 ↦ ?_⟩
  have hτ0 : 0 < Real.sqrt (2 * lam) := Real.sqrt_pos.2 (by linarith)
  have hτ1 : Real.sqrt (2 * lam) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith
  obtain ⟨A, hA, hcorr⟩ := hD (Real.sqrt (2 * lam)) hτ0 hτ1 ⌈(t : ℝ) / lam ^ 2⌉₊ γ hγ0 hγ1
  exact ⟨A, hA, fun G hreg ht ↦ hcorr G hreg (card_eig_le_neg_sqrt_le G hl0 hl1 ht)⟩

/-! ### The parameters, for the corollaries -/

open Classical in
/-- **The parameters of Theorem 7.20** for `c`, `λ`, `t` and `γ`: the algorithm
`BHSV25.Alg.indepAlgGS p` has the guarantee of Theorem 7.20. -/
theorem exists_indep_params {c : ℝ} (hc : 0 < c) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    (t : ℕ) {γ : ℝ} (hγ0 : 0 < γ) :
    ∃ p : ℕ × ℕ × ℕ × ℕ, ∀ G : Graph, G.IsRegular →
      (Finset.univ.filter fun i ↦ G.eig i ≤ -lam).card ≤ t →
      G.HasIndepSet ((1 / 2 - γ) * G.1) →
        (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * G.1 ≤
          (G.vertexSet (indepAlgGS p (G.1, adjTable G))).card := by
  obtain ⟨c₁, hc₁⟩ : ∃ x : ℝ, x = min c 1 := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := hc₁ ▸ lt_min hc one_pos
  have hc₁1 : c₁ ≤ 1 := hc₁ ▸ min_le_right _ _
  have hc₁c : c₁ ≤ c := hc₁ ▸ min_le_left _ _
  obtain ⟨cc, hcc⟩ : ∃ x : ℝ, x = c₁ / 32 := ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ x : ℝ, x = 32 * (1 + 32 / c₁) / c + 1 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ x : ℝ, x = 1 + (1 - lam) / γ := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈A₁ * W⌉₊ := ⟨_, rfl⟩
  have hKge : A₁ * W ≤ K := hK ▸ Nat.le_ceil _
  have hA₁1 : 1 ≤ A₁ := by
    have : 0 ≤ 32 * (1 + 32 / c₁) / c := by positivity
    rw [hA₁]
    linarith
  have hW1 : 1 ≤ W := by
    rw [hW]
    have : 0 ≤ (1 - lam) / γ := div_nonneg (by linarith) hγ0.le
    linarith
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ K := le_trans (by nlinarith) hKge
    exact_mod_cast this
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = ⌈8 / cc * (t + 2 + K / 2 : ℝ)⌉₊ := ⟨_, rfl⟩
  have hage : 8 / cc * (t + 2 + K / 2 : ℝ) ≤ a := ha ▸ Nat.le_ceil _
  exact ⟨(a, t, (Nat.sqrt t + 1) * K, (3 + 12 * K) ^ t), fun G hreg ht hInd ↦
    card_indepAlgGS_final G hreg hl0 hl1 ht hc hc₁0 hc₁1 hc₁c hcc hγ0 hA₁ hW hK1 hKge hage hInd⟩

/-- **The parameters of Corollary 7.21** for `c`, `λ < 1/2`, `t` and `γ`. -/
theorem exists_indep_params_top {c : ℝ} (hc : 0 < c) {lam : ℝ} (hl0 : 0 < lam)
    (hl1 : lam < 1 / 2) (t : ℕ) {γ : ℝ} (hγ0 : 0 < γ) :
    ∃ p : ℕ × ℕ × ℕ × ℕ, ∀ G : Graph, G.IsRegular → G.numEigGT lam ≤ t →
      G.HasIndepSet ((1 / 2 - γ) * G.1) →
        (1 / 2 - γ - (4 + c) * γ / (1 - Real.sqrt (2 * lam))) * G.1 ≤
          (G.vertexSet (indepAlgGS p (G.1, adjTable G))).card := by
  have hτ0 : 0 < Real.sqrt (2 * lam) := Real.sqrt_pos.2 (by linarith)
  have hτ1 : Real.sqrt (2 * lam) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith
  obtain ⟨p, hp⟩ := exists_indep_params hc hτ0 hτ1 ⌈(t : ℝ) / lam ^ 2⌉₊ hγ0
  exact ⟨p, fun G hreg ht hInd ↦ hp G hreg (card_eig_le_neg_sqrt_le G hl0 hl1 ht) hInd⟩

end BHSV25.Alg
