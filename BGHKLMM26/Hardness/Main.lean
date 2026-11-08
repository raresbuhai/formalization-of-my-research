module

public import BGHKLMM26.Hardness.Glue
public import BGHKLMM26.Hardness.SparsifyMain
public import BGHKLMM26.Hardness.KKMORobust
public import BGHKLMM26.Hardness.Machine
public import BGHKLMM26.Hardness.Enlarge
public import BGHKLMM26.GW
public import Complexity.Computability.Probabilistic.Sampling

/-!
# Theorem 1.2, assuming the robust Majority is Stablest theorem

`BGHKLMM26.Hard.maxCut_hardness_of_robustMIS`: Theorem 1.2 of [BGHKLMM26], with `log d / d` in
place of the paper's `log² d / d`, from `BGHKLMM26.Hard.RobustMIS` ([BGHKLMM26, Theorem 7.1], with
the error `C √η`).

The reduction (`BGHKLMM26.Hard.redProg`) samples `n D` edges of the KKMO graph with correlation
`ρ_d`, a dyadic rational close to `ρ*`, and caps the degrees at `d`, `D = ⌊d/10⌋`. A yes-instance
of Unique Games goes to a yes-instance of Max-Cut with probability `9/10`
(`BGHKLMM26.Hard.yes_case`), and a no-instance to a no-instance (`BGHKLMM26.Hard.no_case`). With
the alphabet enlargement this is a randomized reduction from an NP-hard problem, so a
polynomial-time algorithm with bounded error for the gap problem would put `NP` in `BPP`.
-/

@[expose] public section

namespace BGHKLMM26.Hard

open UniqueGames

open Finset Cslib Cslib.Complexity Cslib.Probability
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad

/-! ### The program -/

/-- **The reduction** as a probabilistic program: read `coinCount` coins and run `reduce`. -/
noncomputable def redProg (P : Prm) (G : UGInstance) : ProbComp Graph :=
  (fun w ↦ reduce P (G, w)) <$> BitString.sampleList (P.coinCount G)

theorem redProg_isPPTOn (P : Prm) : IsPPTOn encUG encGraph (redProg P) :=
  IsPPTOn.of_seeded (coinCount_polytime P) (reduce_polytime P)

/-- On instances that fail the check, the output is the single vertex. -/
theorem prob_redProg_not_ok {P : Prm} {G : UGInstance} (hok : P.ok G = false) {Y : Set Graph}
    (hY : pointGraph ∈ Y) : ((ProbComp.eval (redProg P G)).toOuterMeasure Y).toReal = 1 := by
  have hconst : (fun w ↦ reduce P (G, w)) = fun _ ↦ pointGraph := by
    funext w; simp [reduce, hok]
  unfold redProg
  rw [hconst, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
  have : (fun _ : List Bool ↦ pointGraph) ⁻¹' Y = Set.univ := Set.eq_univ_of_forall fun _ ↦ hY
  rw [this, (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)]
  rfl

/-! ### The sparsification at a given `D` -/

/-- The conclusion of `BGHKLMM26.Hard.sparsify_yes` at `D`. -/
def SparsifyYesAt (C₀ : ℝ) (D n₀ : ℕ) : Prop :=
  ∀ n : ℕ, n₀ ≤ n → ∀ Δ : ℕ, 10 * D ≤ Δ → ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω]
    (dec : Ω → Fin n × Fin n),
      (∀ a, frac (fun ω ↦ (dec ω).1 = a ∨ (dec ω).2 = a) ≤ 3 / n) →
      (∀ e, frac (fun ω ↦ dec ω = e) ≤ 1 / (n * D ^ 2)) →
      ∀ (c : ℝ) (f : Fin n → Bool), c ≤ lawCut dec f →
        9 / 10 ≤ frac fun ω : Fin (n * D) → Ω ↦
          c - C₀ / D ≤ maxCutValue (sampledGraph n Δ dec ω)

/-- The conclusion of `BGHKLMM26.Hard.sparsify_no` at `D`. -/
def SparsifyNoAt (C₁ η₀ C₀ A₀ : ℝ) (D n₀ : ℕ) : Prop :=
  ∀ n : ℕ, n₀ ≤ n → ∀ Δ : ℕ, 10 * D ≤ Δ →
    ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (dec : Ω → Fin n × Fin n),
    (∀ a, frac (fun ω ↦ (dec ω).1 = a ∨ (dec ω).2 = a) ≤ 3 / n) →
    (∀ e, frac (fun ω ↦ dec ω = e) ≤ 1 / (n * D ^ 2)) →
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (∀ f, lawCut dec f ≤ s + lam C₁ D / 2) →
    ∀ 𝓛 : Finset (Fin n → Bool), (𝓛.card : ℝ) ≤ Real.exp (n / A₀) →
    (∀ (f : Fin n → Bool) (η : ℝ), lam C₁ D ≤ η → η ≤ η₀ → s - η ≤ lawCut dec f →
      ∃ L ∈ 𝓛, ((univ.filter fun a ↦ f a ≠ L a).card : ℝ) ≤ C₁ * Real.sqrt η * n) →
    9 / 10 ≤ frac fun ω : Fin (n * D) → Ω ↦
      maxCutValue (sampledGraph n Δ dec ω) ≤ s + C₀ * lam C₁ D

theorem sparsify_yes_at : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ D : ℕ, 1 ≤ D → ∃ n₀ : ℕ, SparsifyYesAt C₀ D n₀ :=
  sparsify_yes

theorem sparsify_no_at {C₁ η₀ : ℝ} (hC₁ : 0 < C₁) (hη₀ : 0 < η₀) (hη₀1 : η₀ < 1) :
    ∃ (C₀ : ℝ) (D₀ : ℕ), 0 < C₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∃ (A₀ : ℝ) (n₀ : ℕ), 0 < A₀ ∧
      SparsifyNoAt C₁ η₀ C₀ A₀ D n₀ :=
  sparsify_no hC₁ hη₀ hη₀1

/-! ### The cases -/

theorem kkmoCut_congr {ρ : ℝ} {R : ℕ} {cs : List UGConstraint} {nV : ℕ}
    (hv : ∀ c ∈ cs, c.1.2 < nV) {f f' : ℕ → Cube (Fin R) → Bool}
    (h : ∀ v < nV, ∀ x, f v x = f' v x) : kkmoCut ρ R cs f = kkmoCut ρ R cs f' := by
  unfold kkmoCut
  congr 1
  refine congrArg List.sum (List.map_congr_left fun c₁ hc₁ ↦ ?_)
  congr 1
  refine congrArg List.sum (List.map_congr_left fun c₂ hc₂ ↦ ?_)
  have hc₂' : c₂ ∈ cs := (List.mem_filter.1 hc₂).1
  congr 1
  funext x y
  rw [h _ (hv c₁ hc₁), h _ (hv c₂ hc₂')]

theorem two_pow_le_nVert {P : Prm} {G : UGInstance} (hG : GoodI P.R G) (hok : P.ok G = true) :
    2 ^ P.R ≤ P.nVert G := by
  have hcs : G.2.2.2 ≠ [] := List.length_pos_iff.1 (ok_iff.1 hok).2.1
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hcs
  have hV1 : 0 < G.2.1 := Nat.zero_lt_of_lt (hG.1 c hc).2.1
  rw [nVert_eq hok]
  exact Nat.le_mul_of_pos_left _ hV1

theorem tv_le_two_pow {P : Prm} {G : UGInstance} (hG : GoodI P.R G) (hok : P.ok G = true) :
    1 / (2 * (P.nVert G : ℝ) * 2 ^ P.Δ) ≤ 1 / 2 ^ P.Δ := by
  have h1 : (1 : ℝ) ≤ P.nVert G := by
    have := two_pow_le_nVert hG hok
    exact_mod_cast (Nat.one_le_two_pow).trans this
  apply one_div_le_one_div_of_le (by positivity)
  have : (0 : ℝ) < 2 ^ P.Δ := by positivity
  nlinarith

/-- **Completeness**: a yes-instance of Unique Games goes to a graph of Max-Cut value at least
`(1 - ρ)/2 - 2ε - 2^-Δ - C₀/D`, and maximum degree at most `Δ`, with probability `9/10`. -/
theorem yes_case {P : Prm} {G : UGInstance} (hG : GoodI P.R G) (hq : P.q ≤ 2 ^ P.b)
    {ε : ℝ} (hval : 1 - ε ≤ ugValue G) (hε1 : ε < 1)
    {C₀ : ℝ} {n₀ : ℕ} (hS : SparsifyYesAt C₀ P.D n₀) (hn₀ : n₀ ≤ 2 ^ P.R)
    (hΔ : 10 * P.D ≤ P.Δ) (hD : 1 ≤ P.D)
    (hκ : ((1 + |P.rho|) / 2) ^ P.R ≤ 1 / (2 * P.D ^ 2)) (hΔ2 : P.D ^ 2 ≤ 2 ^ P.Δ)
    {c s : ℝ} (hc : c ≤ (1 - P.rho) / 2 - 2 * ε - 1 / 2 ^ P.Δ - C₀ / P.D) :
    9 / 10 ≤ ((ProbComp.eval (redProg P G)).toOuterMeasure (maxCutGap P.Δ c s).yes).toReal := by
  have hcs : G.2.2.2 ≠ [] := by
    intro h; rw [Enlarge.ugValue_eq_zero_of_nil h] at hval; linarith
  have hok := ok_of_good hG hcs
  obtain ⟨f', hf'⟩ := kkmo_complete (rho_mem hq).1 (rho_mem hq).2 hG hval
  obtain ⟨f, hf⟩ := exists_cut_of_tables P.R G.2.1 (nVert_eq hok) f'
  have hcong : kkmoCut P.rho P.R G.2.2.2 (fun v y ↦ liftCut f (vtx v y)) =
      kkmoCut P.rho P.R G.2.2.2 f' :=
    kkmoCut_congr (fun c hc ↦ (hG.1 c hc).2.1) hf
  have hlaw := abs_lawCut_dec_sub_le hq hG hok f
  rw [hcong] at hlaw
  have htv := tv_le_two_pow hG hok
  have hlow : (1 - P.rho) / 2 - 2 * ε - 1 / 2 ^ P.Δ ≤ lawCut (dec hG hok) f := by
    linarith [(abs_le.1 hlaw).1]
  have hS' := hS (P.nVert G) (hn₀.trans (two_pow_le_nVert hG hok)) P.Δ hΔ _ (dec hG hok)
    (dec_touch hq hG hok) (dec_maxw hq hG hok hκ hΔ2 hD) _ f hlow
  unfold redProg
  rw [prob_reduce hG hok]
  refine hS'.trans (frac_le_of_imp fun ω hω ↦ ?_)
  refine ⟨?_, maxDegree_sampledGraph _ _ _ _⟩
  beta_reduce at hω ⊢
  change c ≤ maxCutValue (sampledGraph (P.nVert G) P.Δ (dec hG hok) ω)
  linarith

theorem card_ltfCuts_le_exp {R nV n : ℕ} (hn : n = nV * 2 ^ R) {A₀ : ℝ}
    (hA : ((2 ^ R + 1) ^ (R + 1) : ℝ) ≤ Real.exp (2 ^ R / A₀)) :
    ((ltfCuts R nV hn).card : ℝ) ≤ Real.exp (n / A₀) := by
  have h1 : ((ltfCuts R nV hn).card : ℝ) ≤ (((2 ^ R + 1) ^ (R + 1) : ℕ) : ℝ) ^ nV := by
    exact_mod_cast card_ltfCuts_le R nV hn
  push_cast at h1
  refine h1.trans ?_
  calc (((2 : ℝ) ^ R + 1) ^ (R + 1)) ^ nV ≤ (Real.exp (2 ^ R / A₀)) ^ nV :=
        pow_le_pow_left₀ (by positivity) hA _
    _ = Real.exp (n / A₀) := by
        rw [← Real.exp_nat_mul, hn]; push_cast; ring_nf

/-- **Soundness**: a no-instance of Unique Games goes to a graph of Max-Cut value at most
`s + C₀ λ` and maximum degree at most `Δ` with probability `9/10`, given the soundness and the
robust inverse of soundness of the dense graph. -/
theorem no_case {P : Prm} {G : UGInstance} (hG : GoodI P.R G) (hq : P.q ≤ 2 ^ P.b)
    {C₁ η₀ C₀ A₀ : ℝ} {n₀ : ℕ} (hS : SparsifyNoAt C₁ η₀ C₀ A₀ P.D n₀) (hn₀ : n₀ ≤ 2 ^ P.R)
    (hΔ : 10 * P.D ≤ P.Δ) (hD : 1 ≤ P.D)
    (hκ : ((1 + |P.rho|) / 2) ^ P.R ≤ 1 / (2 * P.D ^ 2)) (hΔ2 : P.D ^ 2 ≤ 2 ^ P.Δ)
    (hA : ((2 ^ P.R + 1) ^ (P.R + 1) : ℝ) ≤ Real.exp (2 ^ P.R / A₀))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (htv : 1 / 2 ^ P.Δ ≤ lam C₁ P.D / 4)
    (hsnd : ∀ f', kkmoCut P.rho P.R G.2.2.2 f' ≤ s + lam C₁ P.D / 4)
    (hrob : ∀ (f' : ℕ → Cube (Fin P.R) → Bool) (η : ℝ), lam C₁ P.D ≤ η → η ≤ η₀ →
      s - η - lam C₁ P.D / 4 ≤ kkmoCut P.rho P.R G.2.2.2 f' →
      (∑ v ∈ range G.2.1, ltfDist (fun x ↦ bitVal (f' v x))) / G.2.1 ≤ C₁ * Real.sqrt η)
    {c s' : ℝ} (hs' : s + C₀ * lam C₁ P.D ≤ s') (hs'0 : 0 ≤ s') (hsc : s' < c) :
    9 / 10 ≤ ((ProbComp.eval (redProg P G)).toOuterMeasure (maxCutGap P.Δ c s').no).toReal := by
  by_cases hok : P.ok G = true
  swap
  · rw [Bool.not_eq_true] at hok
    rw [prob_redProg_not_ok hok]
    · norm_num
    · exact ⟨⟨by rw [maxCutValue_pointGraph]; exact hs'0, hsc⟩, maxDegree_pointGraph _⟩
  have hcs : G.2.2.2 ≠ [] := List.length_pos_iff.1 (ok_iff.1 hok).2.1
  have hn := nVert_eq hok
  obtain ⟨c₀, hc₀⟩ := List.exists_mem_of_ne_nil _ hcs
  have hV1 : 0 < G.2.1 := Nat.zero_lt_of_lt (hG.1 c₀ hc₀).2.1
  have hVr : (0 : ℝ) < G.2.1 := by exact_mod_cast hV1
  have htv' := tv_le_two_pow hG hok
  have hlaw (f : Fin (P.nVert G) → Bool) := abs_lawCut_dec_sub_le hq hG hok f
  have hupper : ∀ f, lawCut (dec hG hok) f ≤ s + lam C₁ P.D / 2 := fun f ↦ by
    have := hsnd (fun v y ↦ liftCut f (vtx v y))
    linarith [(abs_le.1 (hlaw f)).2]
  have hcover : ∀ (f : Fin (P.nVert G) → Bool) (η : ℝ), lam C₁ P.D ≤ η → η ≤ η₀ →
      s - η ≤ lawCut (dec hG hok) f →
      ∃ L ∈ ltfCuts P.R G.2.1 hn, ((univ.filter fun a ↦ f a ≠ L a).card : ℝ) ≤
        C₁ * Real.sqrt η * P.nVert G := by
    intro f η hη1 hη2 hcut
    have hk : s - η - lam C₁ P.D / 4 ≤
        kkmoCut P.rho P.R G.2.2.2 (fun v y ↦ liftCut f (vtx v y)) := by
      linarith [(abs_le.1 (hlaw f)).2]
    have havg := hrob _ η hη1 hη2 hk
    obtain ⟨L, hL, hcard⟩ := exists_ltfCut_near P.R G.2.1 hn f
    refine ⟨L, hL, ?_⟩
    rw [hcard]
    have hnr : (P.nVert G : ℝ) = G.2.1 * 2 ^ P.R := by rw [hn]; push_cast; ring
    rw [div_le_iff₀ hVr] at havg
    rw [hnr]
    nlinarith [show (0 : ℝ) < 2 ^ P.R by positivity]
  have hS' := hS (P.nVert G) (hn₀.trans (two_pow_le_nVert hG hok)) P.Δ hΔ _ (dec hG hok)
    (dec_touch hq hG hok) (dec_maxw hq hG hok hκ hΔ2 hD) s hs0 hs1 hupper
    (ltfCuts P.R G.2.1 hn) (card_ltfCuts_le_exp hn hA) hcover
  unfold redProg
  rw [prob_reduce hG hok]
  refine hS'.trans (frac_le_of_imp fun ω hω ↦ ?_)
  beta_reduce at hω
  exact ⟨⟨by change maxCutValue (sampledGraph (P.nVert G) P.Δ (dec hG hok) ω) ≤ s'; linarith,
    hsc⟩, maxDegree_sampledGraph _ _ _ _⟩

/-! ### Arithmetic -/

/-- A dyadic correlation just above `ρ`. -/
theorem exists_dyadic {ρ θ : ℝ} (hρ0 : -1 ≤ ρ) (hρ1 : ρ ≤ 1) (hθ : 0 < θ) :
    ∃ b q : ℕ, q ≤ 2 ^ b ∧ ρ ≤ 1 - 2 * q / 2 ^ b ∧ 1 - 2 * q / 2 ^ b ≤ ρ + θ := by
  obtain ⟨b, hb⟩ := pow_unbounded_of_one_lt (2 / θ) (by norm_num : (1 : ℝ) < 2)
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  set X : ℝ := (1 - ρ) / 2 * 2 ^ b with hX
  have hX0 : 0 ≤ X := by rw [hX]; nlinarith
  have hX1 : X ≤ 2 ^ b := by rw [hX]; nlinarith
  refine ⟨b, ⌊X⌋₊, ?_, ?_, ?_⟩
  · have := Nat.floor_le hX0
    exact_mod_cast this.trans hX1
  · have := Nat.floor_le hX0
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ h2b]
    rw [hX] at this
    nlinarith
  · have := Nat.lt_floor_add_one X
    have hθb : 2 / 2 ^ b ≤ θ := by
      rw [div_le_iff₀ h2b]
      rw [div_lt_iff₀ hθ] at hb
      linarith
    have : 1 - ρ - 2 / 2 ^ b ≤ 2 * ⌊X⌋₊ / 2 ^ b := by
      rw [le_div_iff₀ h2b, sub_mul, div_mul_cancel₀ _ h2b.ne']
      rw [hX] at this
      nlinarith
    linarith

theorem one_lt_log_of_three_le {D : ℕ} (hD : 3 ≤ D) : 1 < Real.log D := by
  rw [Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < D by omega))]
  have : (3 : ℝ) ≤ D := by exact_mod_cast hD
  linarith [Real.exp_one_lt_d9]

theorem lam_pos (C₁ : ℝ) {D : ℕ} (hD : 3 ≤ D) : 0 < lam C₁ D :=
  lam_pos_of_log (by exact_mod_cast (show 0 < D by omega)) (one_lt_log_of_three_le hD).le

theorem inv_le_lam (C₁ : ℝ) {D : ℕ} (hD : 3 ≤ D) : 1 / (D : ℝ) ≤ lam C₁ D :=
  one_div_le_lam (by exact_mod_cast (show 0 < D by omega)) (one_lt_log_of_three_le hD).le

/-- `λ_D ≤ 20 K log d / d` for `D = ⌊d/10⌋`. -/
theorem lam_le (C₁ : ℝ) {d : ℕ} (hd : 30 ≤ d) :
    lam C₁ (d / 10) ≤ 20 * lamK C₁ * Real.log d / d := by
  have hDr : (0 : ℝ) < (d / 10 : ℕ) := by exact_mod_cast (show 0 < d / 10 by omega)
  have hdr : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hDd : ((d / 10 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.div_le_self d 10
  have h20 : (d : ℝ) ≤ 20 * (d / 10 : ℕ) := by
    have : d ≤ 20 * (d / 10) := by omega
    exact_mod_cast this
  have hlog : Real.log (d / 10 : ℕ) ≤ Real.log d := Real.log_le_log hDr hDd
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast (show 1 ≤ d by omega))
  have hK : 0 ≤ lamK C₁ := zero_le_one.trans (one_le_lamK C₁)
  unfold lam
  rw [div_le_div_iff₀ hDr hdr]
  calc lamK C₁ * Real.log (d / 10 : ℕ) * d
      ≤ lamK C₁ * Real.log d * (20 * (d / 10 : ℕ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlog hK) h20 hdr.le (by positivity)
    _ = 20 * lamK C₁ * Real.log d * (d / 10 : ℕ) := by ring

theorem inv_div_ten_le {d : ℕ} (hd : 30 ≤ d) : 1 / ((d / 10 : ℕ) : ℝ) ≤ 20 / d := by
  have hDr : (0 : ℝ) < (d / 10 : ℕ) := by exact_mod_cast (show 0 < d / 10 by omega)
  have hdr : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h20 : (d : ℝ) ≤ 20 * (d / 10 : ℕ) := by
    have : d ≤ 20 * (d / 10) := by omega
    exact_mod_cast this
  rw [div_le_div_iff₀ hDr hdr]
  linarith

theorem pow_two_ge {d : ℕ} (hd : 4 ≤ d) : d ^ 2 ≤ 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ 2 n]
    nlinarith

/-- Eventually `A (R+1)² ≤ 2^R`. -/
theorem eventually_sq_le_two_pow (A : ℝ) : ∃ R₀ : ℕ, ∀ R ≥ R₀, A * ((R : ℝ) + 1) ^ 2 ≤ 2 ^ R := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)
  have hA : (0 : ℝ) < 1 / (4 * (|A| + 1)) := by positivity
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.1 (h.eventually (gt_mem_nhds hA))
  refine ⟨max R₁ 1, fun R hR ↦ ?_⟩
  have h1 := hR₁ R (le_of_max_le_left hR)
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast le_of_max_le_right hR
  have h2R : (0 : ℝ) < 2 ^ R := by positivity
  rw [div_lt_iff₀ h2R] at h1
  have hsq : ((R : ℝ) + 1) ^ 2 ≤ 4 * (R : ℝ) ^ 2 := by nlinarith
  have hAabs : A ≤ |A| := le_abs_self A
  have : (|A| + 1) * (4 * (R : ℝ) ^ 2) < 2 ^ R := by
    have := mul_lt_mul_of_pos_left h1 (show (0 : ℝ) < 4 * (|A| + 1) by positivity)
    rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
    nlinarith
  nlinarith [sq_nonneg ((R : ℝ) + 1), abs_nonneg A]

/-- The number of LTFs is small next to `2^R`: `(2^R + 1)^(R+1) ≤ exp(2^R / A)` once
`A (R+1)² ≤ 2^R`. -/
theorem ltf_count_le_exp {R : ℕ} {A : ℝ} (hA : 0 < A) (h : A * ((R : ℝ) + 1) ^ 2 ≤ 2 ^ R) :
    ((2 : ℝ) ^ R + 1) ^ (R + 1) ≤ Real.exp (2 ^ R / A) := by
  have h1 : (2 : ℝ) ^ R + 1 ≤ Real.exp (R + 1) := by
    have : (2 : ℝ) ^ R + 1 ≤ 2 ^ (R + 1) := by
      rw [pow_succ]; have := one_le_pow₀ (M₀ := ℝ) (show (1 : ℝ) ≤ 2 by norm_num) (n := R)
      linarith
    refine this.trans ?_
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.2
    push_cast
    have := Real.log_two_lt_d9
    nlinarith
  calc ((2 : ℝ) ^ R + 1) ^ (R + 1) ≤ (Real.exp (R + 1)) ^ (R + 1) :=
        pow_le_pow_left₀ (by positivity) h1 _
    _ = Real.exp (((R : ℝ) + 1) ^ 2) := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
    _ ≤ Real.exp (2 ^ R / A) := by
        apply Real.exp_le_exp.2
        rw [le_div_iff₀ hA]
        linarith

/-- **The robust inverse at a nearby correlation**: from the robust inverse of soundness at `ρ`,
with `ξ = √λ`, the cuts at `ρ'` with `|Cut_ρ' - Cut_ρ| ≤ λ/8` satisfy the bound of
`BGHKLMM26.Hard.no_case` with `C₁ = 2C + 1`. -/
theorem hrob_of_robust {R : ℕ} {G : UGInstance} {ρ ρ' CK ηK lam' η₀' : ℝ}
    (hlam0 : 0 < lam') (hη₀ : η₀' ≤ ηK / 2) (hCK : 0 ≤ CK)
    (hrob : ∀ (f : ℕ → Cube (Fin R) → Bool) (η : ℝ), 0 ≤ η → η ≤ ηK →
        Real.arccos ρ / Real.pi - η ≤ kkmoCut ρ R G.2.2.2 f →
        (∑ v ∈ range G.2.1, ltfDist (fun x ↦ bitVal (f v x))) / G.2.1 ≤
          CK * Real.sqrt η + Real.sqrt lam')
    (hlip : ∀ f, |kkmoCut ρ' R G.2.2.2 f - kkmoCut ρ R G.2.2.2 f| ≤ lam' / 8) :
    ∀ (f : ℕ → Cube (Fin R) → Bool) (η : ℝ), lam' ≤ η → η ≤ η₀' →
      Real.arccos ρ / Real.pi - η - lam' / 4 ≤ kkmoCut ρ' R G.2.2.2 f →
      (∑ v ∈ range G.2.1, ltfDist (fun x ↦ bitVal (f v x))) / G.2.1 ≤
        (2 * CK + 1) * Real.sqrt η := by
  intro f η hη1 hη2 hcut
  have hη0 : 0 ≤ η := hlam0.le.trans hη1
  have h' := hrob f (η + 3 * lam' / 8) (by positivity) (by linarith)
    (by linarith [(abs_le.1 (hlip f)).2])
  have hs1 : √(η + 3 * lam' / 8) ≤ √(η + η) := Real.sqrt_le_sqrt (by linarith)
  have hs2 : √(η + η) ≤ √η + √η := KKMORobust.sqrt_add_le_add_sqrt' hη0 hη0
  have hs3 : √lam' ≤ √η := Real.sqrt_le_sqrt hη1
  have : CK * √(η + 3 * lam' / 8) ≤ CK * (2 * √η) :=
    mul_le_mul_of_nonneg_left (by linarith) hCK
  linarith

/-! ### Theorem 1.2 -/

theorem gap_pos : Real.arccos GW.rhoStar / Real.pi < (1 - GW.rhoStar) / 2 := by
  have hw := GW.rhoStar_mem_window
  have h1 : 0 < (1 - GW.rhoStar) / 2 := by linarith [hw.1, hw.2]
  have h2 : gwRatio GW.rhoStar < 1 := GW.alphaGW_eq ▸ GW.alphaGW_lt_one
  unfold gwRatio at h2
  rwa [div_lt_one h1] at h2

theorem eventually_small (C γ K : ℝ) (hγ : 0 < γ) :
    ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → C * (Real.log d + 1) / d < γ ∧
      K * Real.log d / d < 1 / 7 := by
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h1' : Filter.Tendsto (fun x : ℝ ↦ Real.log x / x) Filter.atTop (nhds 0) := by
    simpa using h1
  have h2 : Filter.Tendsto (fun x : ℝ ↦ Real.log x / x + 1 / x) Filter.atTop (nhds 0) := by
    simpa using h1'.add (tendsto_inv_atTop_zero.congr fun x ↦ (one_div x).symm)
  have h3 := (h2.comp tendsto_natCast_atTop_atTop)
  have h4 := (h1'.comp tendsto_natCast_atTop_atTop)
  have e3 := Filter.eventually_atTop.1 ((h3.const_mul (|C| + 1)).eventually
    (gt_mem_nhds (show (|C| + 1) * 0 < γ by simpa using hγ)))
  have e4 := Filter.eventually_atTop.1 ((h4.const_mul K).eventually
    (gt_mem_nhds (show K * 0 < 1 / 7 by norm_num)))
  obtain ⟨a, ha⟩ := e3
  obtain ⟨b, hb⟩ := e4
  refine ⟨max (max a b) 2, fun d hd ↦ ⟨?_, ?_⟩⟩
  · have := ha d (le_of_max_le_left (le_of_max_le_left hd))
    simp only [Function.comp_apply] at this
    have hd0 : (0 : ℝ) < d := by
      exact_mod_cast (show 0 < d by have := le_of_max_le_right hd; omega)
    have hlog : 0 ≤ Real.log d / d := by
      have : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast
        (show 1 ≤ d by have := le_of_max_le_right hd; omega))
      positivity
    have hC : C * (Real.log d + 1) / d ≤ (|C| + 1) * (Real.log d / d + 1 / d) := by
      rw [show C * (Real.log d + 1) / d = C * (Real.log d / d + 1 / d) by ring]
      have hpos : 0 ≤ Real.log d / d + 1 / d := by positivity
      nlinarith [le_abs_self C]
    linarith
  · have := hb d (le_of_max_le_right (le_of_max_le_left hd))
    simp only [Function.comp_apply] at this
    rw [mul_div_assoc]; linarith

/-- The correlation of the reduction at degree `d`: a dyadic `ρ_d` just above `ρ*`, close enough
that the cut values and `arccos ρ / π` move by at most `λ/8`. -/
theorem exists_rho_d {M lamD : ℝ} (hM : 0 < M) (hlam0 : 0 < lamD) {d : ℕ} (hdr : (0 : ℝ) < d) :
    ∃ b q : ℕ, q ≤ 2 ^ b ∧ -1 < 1 - 2 * (q : ℝ) / 2 ^ b ∧ 1 - 2 * (q : ℝ) / 2 ^ b < 0 ∧
      |1 - 2 * (q : ℝ) / 2 ^ b| ≤ 9 / 10 ∧
      Real.arccos (1 - 2 * (q : ℝ) / 2 ^ b) / Real.pi ≤
        Real.arccos GW.rhoStar / Real.pi + lamD / 8 ∧
      M * |1 - 2 * (q : ℝ) / 2 ^ b - GW.rhoStar| ≤ lamD / 8 ∧
      GW.rhoStar ≤ 1 - 2 * (q : ℝ) / 2 ^ b ∧ 1 - 2 * (q : ℝ) / 2 ^ b ≤ GW.rhoStar + 1 / d := by
  have hw := GW.rhoStar_mem_window
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1
    (Real.continuous_arccos.continuousAt (x := GW.rhoStar)) (Real.pi * lamD / 8) (by positivity)
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = min (min (δ / 2) (lamD / (8 * M))) (min (1 / 10) (1 / d)) :=
    ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  have hθδ : θ ≤ δ / 2 := by rw [hθdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hθM : θ ≤ lamD / (8 * M) := by rw [hθdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hθ10 : θ ≤ 1 / 10 := by rw [hθdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hθd : θ ≤ 1 / d := by rw [hθdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨b, q, hq, hlo, hhi⟩ := exists_dyadic (ρ := GW.rhoStar) (by linarith [hw.1])
    (by linarith [hw.2]) hθ0
  refine ⟨b, q, hq, ?_⟩
  set ρd : ℝ := 1 - 2 * (q : ℝ) / 2 ^ b with hρd
  have hdiff : |ρd - GW.rhoStar| ≤ θ := abs_le.2 ⟨by linarith, by linarith⟩
  refine ⟨by linarith [hw.1], by linarith [hw.2],
    abs_le.2 ⟨by linarith [hw.1], by linarith [hw.2]⟩, ?_, ?_, hlo, by linarith⟩
  · have h := hδc (show dist ρd GW.rhoStar < δ by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq] at h
    rw [div_add' _ _ _ Real.pi_pos.ne', div_le_div_iff_of_pos_right Real.pi_pos]
    linarith [(abs_lt.1 h).2]
  · calc M * |ρd - GW.rhoStar| ≤ M * θ := mul_le_mul_of_nonneg_left hdiff hM.le
      _ ≤ M * (lamD / (8 * M)) := mul_le_mul_of_nonneg_left hθM hM.le
      _ = lamD / 8 := by field_simp

/-- The completeness arithmetic. -/
theorem yes_arith {C C₀y ε ρs ρd : ℝ} {d D : ℕ} (hdr : (0 : ℝ) < d) (hC₀y : 0 ≤ C₀y)
    (hC : 20 * C₀y + 3 ≤ C) (hρ : ρd ≤ ρs + 1 / d) (hε : ε ≤ 1 / (4 * d))
    (h2d : (d : ℝ) ≤ 2 ^ d) (hinvD : 1 / (D : ℝ) ≤ 20 / d) :
    (1 - ρs) / 2 - C / d ≤ (1 - ρd) / 2 - 2 * ε - 1 / 2 ^ d - C₀y / D := by
  have h1 : 1 / (2 : ℝ) ^ d ≤ 1 / d := one_div_le_one_div_of_le hdr h2d
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / d := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have e2 : 1 / (4 * (d : ℝ)) = u / 4 := by rw [hu]; field_simp
  have e4 : C₀y / D ≤ C₀y * (20 * u) := by
    rw [div_eq_mul_one_div, hu]
    exact mul_le_mul_of_nonneg_left (hinvD.trans_eq (by ring)) hC₀y
  have e5 : (20 * C₀y + 3) * u ≤ C * u := mul_le_mul_of_nonneg_right hC hu0
  have e6 : C / (d : ℝ) = C * u := by rw [hu]; ring
  rw [e2] at hε
  rw [← hu] at hρ h1
  rw [e6]
  linarith only [hρ, hε, h1, e4, e5, hu0]

/-- The soundness arithmetic: `s + C₀ λ ≤ s + C log d / d < c* - C/d`. -/
theorem no_arith {C C₀n K lamD ss cs : ℝ} {d : ℕ} (hdr : (0 : ℝ) < d) (hC₀n : 0 ≤ C₀n)
    (hC : K * C₀n ≤ C) (hlog0 : 0 ≤ Real.log d) (hlamle : lamD ≤ K * Real.log d / d)
    (hsmall : C * (Real.log d + 1) / d < cs - ss) :
    ss + C₀n * lamD ≤ ss + C * Real.log d / d ∧
      ss + C * Real.log d / d < cs - C / d := by
  constructor
  · have h1 : C₀n * lamD ≤ C₀n * (K * Real.log d / d) :=
      mul_le_mul_of_nonneg_left hlamle hC₀n
    have h2 : C₀n * (K * Real.log d / d) ≤ C * Real.log d / d := by
      rw [show C₀n * (K * Real.log d / d) = (K * C₀n) * Real.log d / d by ring]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hlog0) hdr.le
    linarith only [h1, h2]
  · have : C * (Real.log d + 1) / d = C * Real.log d / d + C / d := by ring
    rw [this] at hsmall
    linarith only [hsmall]

/-- The facts about `d`, `D = ⌊d/10⌋` and `λ = λ_D` used in the proof. -/
theorem d_facts (C₁ : ℝ) {d D₀n : ℕ} (hd30 : 30 ≤ d) (hdD : 10 * D₀n ≤ d)
    (hlam7 : 20 * lamK C₁ * Real.log d / d < 1 / 7) :
    3 ≤ d / 10 ∧ D₀n ≤ d / 10 ∧ 10 * (d / 10) ≤ d ∧ (d / 10) ^ 2 ≤ 2 ^ d ∧
      0 < lam C₁ (d / 10) ∧ lam C₁ (d / 10) ≤ 20 * lamK C₁ * Real.log d / d ∧
      lam C₁ (d / 10) < 1 / 7 ∧
      1 / ((d / 10 : ℕ) : ℝ) ≤ 20 / d ∧ 1 / 2 ^ d ≤ lam C₁ (d / 10) / 4 ∧ (d : ℝ) ≤ 2 ^ d := by
  have hD3 : 3 ≤ d / 10 := by omega
  have hlamle := lam_le C₁ hd30
  have hinvlam := inv_le_lam C₁ hD3
  have hDr : (0 : ℝ) < (d / 10 : ℕ) := by exact_mod_cast (show 0 < d / 10 by omega)
  have h4D : (4 * (d / 10 : ℕ) : ℝ) ≤ 2 ^ d := by
    have : 4 * (d / 10) ≤ 2 ^ d := by
      have h1 := pow_two_ge (show 4 ≤ d by omega)
      have h2 : d ≤ d ^ 2 := Nat.le_self_pow (by norm_num) d
      omega
    exact_mod_cast this
  refine ⟨hD3, by omega, Nat.mul_div_le d 10, (Nat.pow_le_pow_left (Nat.div_le_self d 10) 2).trans
    (pow_two_ge (by omega)), lam_pos C₁ hD3, hlamle, by linarith, inv_div_ten_le hd30, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have := mul_le_mul_of_nonneg_left hinvlam (show (0 : ℝ) ≤ 4 * (d / 10 : ℕ) by positivity)
    rw [mul_one_div, mul_div_assoc, div_self hDr.ne', mul_one] at this
    nlinarith
  · have : d ≤ 2 ^ d := Nat.lt_two_pow_self.le
    exact_mod_cast this

/-- **Theorem 1.2 at one degree**: the gap problem at degree `d` is the target of a randomized
reduction from an NP-hard problem, given the constants of the analysis. -/
theorem randReducible_at {CK ηK C₀n C₀y M C : ℝ} {D₀n : ℕ}
    (hCK : 0 < CK)
    (hrobK : ∀ ξ : ℝ, 0 < ξ → ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ∀ (R : ℕ) (G : UGInstance), Good R G → ugValue G ≤ ε →
        ∀ (f : ℕ → Cube (Fin R) → Bool) (η : ℝ), 0 ≤ η → η ≤ ηK →
          Real.arccos GW.rhoStar / Real.pi - η ≤ kkmoCut GW.rhoStar R G.2.2.2 f →
          (∑ v ∈ range G.2.1, ltfDist (fun x ↦ bitVal (f v x))) / G.2.1 ≤
            CK * Real.sqrt η + ξ)
    (hSn : ∀ D : ℕ, D₀n ≤ D → ∃ (A₀ : ℝ) (n₀ : ℕ), 0 < A₀ ∧
      SparsifyNoAt (2 * CK + 1) (min (ηK / 2) (1 / 6)) C₀n A₀ D n₀)
    (hSy : ∀ D : ℕ, 1 ≤ D → ∃ n₀ : ℕ, SparsifyYesAt C₀y D n₀)
    (hM : 0 < M) (hlip : ∀ ρ ρ' : ℝ, |ρ| ≤ 9 / 10 → |ρ'| ≤ 9 / 10 → ∀ (R : ℕ) (G : UGInstance),
      Good R G → ∀ f : ℕ → Cube (Fin R) → Bool,
        |kkmoCut ρ' R G.2.2.2 f - kkmoCut ρ R G.2.2.2 f| ≤ M * |ρ' - ρ|)
    (hC : 20 * (C₀y + lamK (2 * CK + 1) * C₀n) + 3 ≤ C) (hC₀n : 0 ≤ C₀n) (hC₀y : 0 ≤ C₀y)
    (hUGC : UGC) {d : ℕ} (hd30 : 30 ≤ d) (hdD : 10 * D₀n ≤ d)
    (hsmall : C * (Real.log d + 1) / d <
      (1 - GW.rhoStar) / 2 - Real.arccos GW.rhoStar / Real.pi)
    (hlam7 : 20 * lamK (2 * CK + 1) * Real.log d / d < 1 / 7) :
    ∃ (R : ℕ) (ε : ℝ), PromiseProblem.NPHard encUG (ugGap R ε ε) ∧
      RandReducible encUG encGraph (ugGap R ε ε)
        (maxCutGap d ((1 - GW.rhoStar) / 2 - C / d)
          (Real.arccos GW.rhoStar / Real.pi + C * Real.log d / d)) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨hD3, hDn, hΔ, hΔ2, hlam0, hlamle, hlam1, hinvD, htv, hd2⟩ :=
    d_facts (2 * CK + 1) hd30 hdD hlam7
  have hKC : 0 ≤ lamK (2 * CK + 1) * C₀n := mul_nonneg (zero_le_one.trans (one_le_lamK _)) hC₀n
  obtain ⟨b, q, hq, hρd1, hρd0, hρdabs, hsd, hMd, -, hhi⟩ := exists_rho_d hM hlam0 hdr
  have hρsabs : |GW.rhoStar| ≤ 9 / 10 := by
    have hw := GW.rhoStar_mem_window
    exact abs_le.2 ⟨by linarith [hw.1], by linarith [hw.2]⟩
  -- `ε`
  obtain ⟨ε₀, hε₀, -, hU⟩ := hUGC
  obtain ⟨ε₁s, hε₁s, hsound⟩ :=
    kkmo_sound hρd1 hρd0 (show 0 < lam (2 * CK + 1) (d / 10) / 8 by positivity)
  have hξr : 0 < Real.sqrt (lam (2 * CK + 1) (d / 10)) := Real.sqrt_pos.2 hlam0
  obtain ⟨ε₁r, hε₁r, hrob⟩ := hrobK _ hξr
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (min ε₀ ε₁s) (min ε₁r (1 / (4 * d))) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have hεε₀ : ε ≤ ε₀ := by rw [hεdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hεs : ε ≤ ε₁s := by rw [hεdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hεr : ε ≤ ε₁r := by rw [hεdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hεd : ε ≤ 1 / (4 * d) := by rw [hεdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hε1 : ε < 1 := by
    have : 1 / (4 * (d : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      have : (30 : ℝ) ≤ d := by exact_mod_cast hd30
      linarith
    linarith
  obtain ⟨R₁, hNP₁⟩ := hU ε hε0 hεε₀
  -- `R`
  obtain ⟨n₀y, hSy'⟩ := hSy (d / 10) (by omega)
  obtain ⟨A₀, n₀n, hA₀, hSn'⟩ := hSn (d / 10) hDn
  have hκ1 : (1 + |1 - 2 * (q : ℝ) / 2 ^ b|) / 2 < 1 := by linarith
  obtain ⟨Ra, hRa⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < 1 / (2 * ((d / 10 : ℕ) : ℝ) ^ 2) by positivity) hκ1
  obtain ⟨Rc, hRc⟩ := eventually_sq_le_two_pow A₀
  obtain ⟨R, hR₀, hNP⟩ := exists_npHard_ge hε1 hε0.le hNP₁ (max (max Ra Rc) (max n₀y n₀n))
  have hRa' : Ra ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR₀
  have hRc' : Rc ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR₀
  have hny : n₀y ≤ 2 ^ R := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    hR₀) Nat.lt_two_pow_self.le
  have hnn : n₀n ≤ 2 ^ R := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    hR₀) Nat.lt_two_pow_self.le
  let P : Prm := ⟨R, b, q, d / 10, d⟩
  have hPrho : P.rho = 1 - 2 * q / 2 ^ b := rfl
  have hκ : ((1 + |P.rho|) / 2) ^ P.R ≤ 1 / (2 * P.D ^ 2) := by
    rw [hPrho]
    exact (pow_le_pow_of_le_one (by positivity) hκ1.le hRa').trans hRa.le
  have hA : ((2 ^ P.R + 1) ^ (P.R + 1) : ℝ) ≤ Real.exp (2 ^ P.R / A₀) :=
    ltf_count_le_exp hA₀ (hRc R hRc')
  refine ⟨R, ε, hNP, redProg P, redProg_isPPTOn P, ?_, ?_⟩
  · -- completeness
    rintro G ⟨hval, hvalid, hRG, hsimple, hbi⟩
    refine yes_case (P := P) ⟨hvalid, hRG, hsimple, hbi⟩ hq hval hε1 hSy' hny hΔ
      (show 1 ≤ d / 10 by omega) hκ hΔ2 ?_
    exact yes_arith hdr hC₀y (by linarith) hhi hεd hd2 hinvD
  · -- soundness
    rintro G ⟨⟨hval, -⟩, hvalid, hRG, hsimple, hbi⟩
    have hG : GoodI P.R G := ⟨hvalid, hRG, hsimple, hbi⟩
    have hss0 : 0 ≤ Real.arccos GW.rhoStar / Real.pi :=
      div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le
    have hss1 : Real.arccos GW.rhoStar / Real.pi ≤ 1 := by
      rw [div_le_one Real.pi_pos]; exact Real.arccos_le_pi _
    have hlog0 : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast (show 1 ≤ d by omega))
    have hCnn : 0 ≤ C := by linarith
    obtain ⟨hs', hsc⟩ := no_arith hdr hC₀n (K := 20 * lamK (2 * CK + 1)) (by linarith) hlog0
      hlamle hsmall
    have hlogd : 0 ≤ C * Real.log d / d := by positivity
    refine no_case (P := P) hG hq hSn' hnn hΔ (show 1 ≤ d / 10 by omega) hκ hΔ2 hA hss0 hss1 htv
      (fun f' ↦ ?_) ?_ hs' (by linarith) hsc
    · have := hsound ε hε0 hεs R G hG hval f'
      exact this.trans (by linarith)
    · refine hrob_of_robust (ρ := GW.rhoStar) hlam0 (min_le_left _ _) hCK.le
        (hrob ε hε0 hεr R G hG hval) fun f ↦ ?_
      exact (hlip GW.rhoStar _ hρsabs hρdabs R G hG f).trans hMd

/-- **Theorem 1.2** of [BGHKLMM26], with `log d / d` in place of the paper's `log² d / d`,
assuming the robust Majority is Stablest theorem with the error `C √η`
(`BGHKLMM26.Hard.RobustMIS`) and the Unique Games Conjecture. -/
theorem maxCut_hardness_of_robustMIS (hMIS : RobustMIS) (hUGC : UGC) :
    ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d → ∀ ρ : ℝ, IsGWMinimizer ρ →
      maxCutGap d ((1 - ρ) / 2 - C / d) (Real.arccos ρ / Real.pi + C * Real.log d / d) ∈
        PromiseBPP encGraph →
      ∀ (α : Type) (enc : α ↪ List Bool), NP enc ⊆ BPP enc := by
  have hw := GW.rhoStar_mem_window
  obtain ⟨CK, ηK, hCK, hηK, hηK1, hrobK⟩ :=
    kkmo_robust hMIS (ρ := GW.rhoStar) (by linarith [hw.1]) (by linarith [hw.2])
  obtain ⟨C₀n, D₀n, hC₀n, hSn⟩ := sparsify_no_at (C₁ := 2 * CK + 1)
    (η₀ := min (ηK / 2) (1 / 6)) (by positivity) (by positivity)
    ((min_le_right _ _).trans_lt (by norm_num))
  obtain ⟨C₀y, hC₀y, hSy⟩ := sparsify_yes_at
  obtain ⟨M, hM, hlip⟩ := kkmoCut_lipschitz (r := 9 / 10) (by norm_num) (by norm_num)
  obtain ⟨d₁, hd₁⟩ := eventually_small (20 * (C₀y + lamK (2 * CK + 1) * C₀n) + 3) _
    (20 * lamK (2 * CK + 1)) (sub_pos.2 gap_pos)
  refine ⟨20 * (C₀y + lamK (2 * CK + 1) * C₀n) + 3, max (max 30 (10 * D₀n)) d₁,
    fun d hd ρ hρ hBPP ↦ ?_⟩
  have hρ' : ρ = GW.rhoStar := GW.exists_unique_isGWMinimizer.unique hρ GW.isGWMinimizer_rhoStar
  subst hρ'
  obtain ⟨hs, hl⟩ := hd₁ d (le_of_max_le_right hd)
  have hd30 : 30 ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
  have hdD : 10 * D₀n ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
  obtain ⟨R, ε, hNP, hred⟩ := randReducible_at hCK hrobK hSn hSy hM hlip le_rfl hC₀n.le hC₀y.le
    hUGC hd30 hdD hs hl
  exact NP_subset_BPP_of_npHard_of_randReducible hNP hred hBPP

end BGHKLMM26.Hard
