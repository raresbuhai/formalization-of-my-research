module

public import BGHKLMM26.IntGap.KS
public import BGHKLMM26.IntGap.Mix
public import BGHKLMM26.IntGap.Sound
public import BGHKLMM26.IntGap.Sample
public import BGHKLMM26.IntGap.Dense
public import BGHKLMM26.IntGap.SoundAt

/-!
# Theorem 1.4

`BGHKLMM26.IntGap.integrality_gap`: [BGHKLMM26, Theorem 1.4] from Theorem 7.1. For large `d`:

* take the soundness data of `BGHKLMM26.IntGap.sound_at` at `d`: a dyadic `ρ_d` near `ρ*`, a number
  of labels `R₀` and a value `ε₀`;
* take `T` with `2^{-T} ≤ 1/d`, `Δ = 4d` scales, `δ = 3 (4/Δ + 2^{-T}) ≤ 6/d`, the largest
  exponent `s = tExp T Δ`, `a` with `2^a ≥ 4 d s`, and `k` large, `z = 2^{k-a}`;
* the instance `kvInst k z` is good with `2^k ≥ R₀` labels and value at most `ε₀`
  (`BGHKLMM26.IntGap.kvInst_value_le`), so the reduction outputs a no-instance with probability
  `9/10`;
* the kernel `Knum` is positive semidefinite with unit diagonal and approximately satisfies the
  triangle inequalities, so mixing gives an SDP solution `v` for all the long-code vertices
  (`BGHKLMM26.IntGap.sdp_of_kernel`); on the dense graph it has value at least
  `(1 - ρ_d)/2 - (δ + 4zs/2^k)/2` (`BGHKLMM26.IntGap.avgExact_Knum_le`), and with probability `9/10`
  the sampled graph keeps it up to `C₀/D` (`BGHKLMM26.IntGap.sparsify_yes_score`);
* both events hold for some coins, and the output graph is the witness.
-/

@[expose] public section

namespace BGHKLMM26.IntGap

open UniqueGames

open scoped RealInnerProductSpace
open Hard Cslib

/-- Two events of probability `9/10` hold together somewhere. -/
theorem exists_of_frac {Ω : Type} [Fintype Ω] {p q : Ω → Prop} (hp : 9 / 10 ≤ frac p)
    (hq : 9 / 10 ≤ frac q) : ∃ ω, p ω ∧ q ω := by
  by_contra hne
  push Not at hne
  have hΩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : frac p = 0 := by simp [frac]
    linarith
  have h1 : frac p ≤ frac fun ω ↦ ¬ q ω := frac_imp_le hne
  rw [frac_not_eq] at h1
  linarith

/-- Large `k` for the soundness of the instance. -/
theorem exists_k_large (a R₀ n₀ : ℕ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) : ∃ k : ℕ, a + 2 ≤ k ∧ R₀ ≤ 2 ^ k ∧
    n₀ ≤ 2 ^ 2 ^ k ∧ (2 : ℝ) ^ (-((k : ℝ) * (2 ^ (k - a) : ℕ)) / (8 * 2 ^ k)) ≤ ε₀ := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 8 * 2 ^ a * (-(Real.log ε₀ / Real.log 2)) ≤ K := exists_nat_ge _
  obtain ⟨k, hk⟩ : ∃ k, k = a + 2 + R₀ + n₀ + K := ⟨_, rfl⟩
  have hk2 : k < 2 ^ k := Nat.lt_two_pow_self
  have hk22 : 2 ^ k < 2 ^ 2 ^ k := Nat.lt_two_pow_self
  refine ⟨k, by omega, by omega, by omega, ?_⟩
  have hka : a ≤ k := by omega
  have hpow : ((2 ^ (k - a) : ℕ) : ℝ) * 2 ^ a = 2 ^ k := by
    push_cast
    rw [← pow_add, Nat.sub_add_cancel hka]
  have hexp : -((k : ℝ) * (2 ^ (k - a) : ℕ)) / (8 * 2 ^ k) = -(k / (8 * 2 ^ a)) := by
    rw [← hpow]
    field_simp
  rw [hexp]
  calc (2 : ℝ) ^ (-(k / (8 * 2 ^ a) : ℝ)) ≤ 2 ^ (Real.log ε₀ / Real.log 2) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [neg_le, le_div_iff₀ (by positivity)]
        have : (K : ℝ) ≤ k := by exact_mod_cast (show K ≤ k by omega)
        linarith
    _ = ε₀ := by
        rw [Real.rpow_def_of_pos (by norm_num), mul_div_cancel₀ _ (Real.log_pos one_lt_two).ne',
          Real.exp_log hε₀]

/-- The parameters `T` and `a`. -/
theorem exists_T_a (d : ℕ) (hd : 1 ≤ d) : ∃ T : ℕ, 8 ≤ T ∧ (1 : ℝ) / 2 ^ T ≤ 1 / d := by
  refine ⟨d + 8, by omega, ?_⟩
  have h1 : d ≤ 2 ^ (d + 8) :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : (d : ℝ) ≤ 2 ^ (d + 8) := by exact_mod_cast h1
  exact one_div_le_one_div_of_le (by exact_mod_cast hd) h2

theorem score_mem {δ K : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hK : |K| ≤ 1) :
    0 ≤ (1 - (1 - δ) * K) / 2 ∧ (1 - (1 - δ) * K) / 2 ≤ 1 := by
  obtain ⟨h1, h2⟩ := abs_le.1 hK
  constructor <;> nlinarith

/-- **The SDP side at given parameters**: an SDP solution for all the long-code vertices of
`kvInst k z` whose value on the sampled graph is at least `c - C₀/D` with probability `9/10`,
`c = (1 - ρ)/2 - (δ + ζ)/2 - 2^{-Δ}`. -/
theorem sdp_event {C₀ : ℝ} {k z T Δs n₀ : ℕ} {P : Prm} (hk1 : 1 ≤ k) (hz2 : 2 * z < 2 ^ k)
    (hT8 : 8 ≤ T) (hΔs1 : 1 ≤ Δs) (hPR : P.R = 2 ^ k) (hq : P.q ≤ 2 ^ P.b) (hρ0 : P.rho ≤ 0)
    (hρ1 : -1 ≤ P.rho) (hGP : GoodI P.R (kvInst k z)) (hok : P.ok (kvInst k z) = true)
    (hcs : (kvInst k z).2.2.2 ≠ []) {δ : ℝ} (hδ : δ = 3 * (4 / Δs + 1 / 2 ^ T)) (hδ1 : δ ≤ 1)
    (hD1 : 1 ≤ P.D) (hΔ : 10 * P.D ≤ P.Δ) (hΔ2 : P.D ^ 2 ≤ 2 ^ P.Δ)
    (hκ : ((1 + |P.rho|) / 2) ^ P.R ≤ 1 / (2 * (P.D : ℝ) ^ 2))
    (hnn₀ : n₀ ≤ P.nVert (kvInst k z))
    (hY : ∀ n : ℕ, n₀ ≤ n →
      ∀ Δ : ℕ, 10 * P.D ≤ Δ → ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (dec : Ω → Fin n × Fin n),
        (∀ a, frac (fun ω ↦ (dec ω).1 = a ∨ (dec ω).2 = a) ≤ 3 / n) →
        (∀ e, frac (fun ω ↦ dec ω = e) ≤ 1 / (n * P.D ^ 2)) →
        ∀ h : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ h i j ∧ h i j ≤ 1) → (∀ i j, h i j = h j i) →
        ∀ c : ℝ, c ≤ mean (fun ω ↦ h (dec ω).1 (dec ω).2) →
          9 / 10 ≤ frac fun ω : Fin (n * P.D) → Ω ↦
            c - C₀ / P.D ≤ edgeAvg ⟨n, sgraph n Δ dec ω⟩ h) :
    ∃ v : Fin (P.nVert (kvInst k z)) → EuclideanSpace ℝ (Fin (P.nVert (kvInst k z))),
      IsSDPSolution _ v ∧
      9 / 10 ≤ frac fun ω : Fin (P.samples (kvInst k z)) → (Fin (P.blockLen (kvInst k z)) → Bool) ↦
        (1 - P.rho) / 2 - (δ + 4 * z / 2 ^ k * tExp T Δs) / 2 - 1 / 2 ^ P.Δ - C₀ / P.D ≤
          sdpValue ⟨P.nVert (kvInst k z), sgraph (P.nVert (kvInst k z)) P.Δ (dec hGP hok) ω⟩ v := by
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  -- the kernel and the SDP solution
  have hKpsd : (Matrix.of fun i j : Fin (P.nVert (kvInst k z)) ↦
      Knum k T Δs ((i : ℕ), (j : ℕ))).PosSemidef :=
    lcK_posSemidef (kvTup k) T Δs (fun i : Fin (P.nVert (kvInst k z)) ↦ lcVert k i)
  obtain ⟨v, hv, hvK⟩ := sdp_of_kernel _ hKpsd (fun i ↦ lcK_self (kvTup k) T hΔs1 _)
    (ε := 4 / Δs + 1 / 2 ^ T) (by positivity) (by rw [hδ]) hδ1
    (fun i j l a ha b hb c hc ↦ approx_triangle (kvTup k) hT8 hΔs1 _ _ _ ha hb hc)
  refine ⟨v, hv, ?_⟩
  -- the score
  have hsc : ∀ e, 0 ≤ (1 - (1 - δ) * Knum k T Δs e) / 2 ∧
      (1 - (1 - δ) * Knum k T Δs e) / 2 ≤ 1 :=
    fun e ↦ score_mem hδ0 hδ1 (abs_lcK_le _ _ _ _ _)
  obtain ⟨h, hh⟩ : ∃ h : Fin (P.nVert (kvInst k z)) → Fin (P.nVert (kvInst k z)) → ℝ,
      ∀ i j, h i j = (1 - (1 - δ) * Knum k T Δs ((i : ℕ), (j : ℕ))) / 2 :=
    ⟨_, fun _ _ ↦ rfl⟩
  have h01 : ∀ i j, 0 ≤ h i j ∧ h i j ≤ 1 := fun i j ↦ by rw [hh]; exact hsc _
  have hsym : ∀ i j, h i j = h j i := fun i j ↦ by rw [hh, hh, Knum_comm]
  -- the mean score on the decoded law
  have hmean : avgExact (P := P) (G := kvInst k z) (fun e ↦ (1 - (1 - δ) * Knum k T Δs e) / 2) -
      1 / 2 ^ P.Δ ≤ mean (fun ω ↦ h (dec hGP hok ω).1 (dec hGP hok ω).2) :=
    (mean_dec_ge hq hGP hok (B := 1)
      (fun e ↦ abs_le.2 ⟨by linarith [(hsc e).1], (hsc e).2⟩)).trans_eq
      (congrArg mean (funext fun ω ↦ (hh _ _).symm))
  have haff : avgExact (P := P) (G := kvInst k z)
      (fun e ↦ (1 - (1 - δ) * Knum k T Δs e) / 2) =
        1 / 2 + (-(1 - δ) / 2) * avgExact (P := P) (G := kvInst k z) (Knum k T Δs) := by
    rw [← avgExact_affine hq hcs]
    exact congrArg _ (funext fun e ↦ by ring)
  have hKle := avgExact_Knum_le (z := z) (T := T) hk1 hz2 hΔs1 hPR hq hρ0
  have hζ0 : (0 : ℝ) ≤ 4 * z / 2 ^ k * tExp T Δs := by positivity
  have hc : (1 - P.rho) / 2 - (δ + 4 * z / 2 ^ k * tExp T Δs) / 2 - 1 / 2 ^ P.Δ ≤
      mean (fun ω ↦ h (dec hGP hok ω).1 (dec hGP hok ω).2) := by
    have h1 := mul_le_mul_of_nonneg_left hKle (by linarith : (0 : ℝ) ≤ 1 - δ)
    have h2 : 0 ≤ δ * (P.rho + 1) := mul_nonneg hδ0 (by linarith)
    have h3 : 0 ≤ 4 * z / 2 ^ k * tExp T Δs * (1 + (1 - δ) * P.rho) :=
      mul_nonneg hζ0 (by nlinarith [mul_nonneg hδ0 (neg_nonneg.2 hρ0)])
    rw [haff] at hmean
    linarith
  -- the sampled graph
  have key := hY _ hnn₀ P.Δ hΔ _ (dec hGP hok) (dec_touch hq hGP hok)
    (dec_maxw hq hGP hok hκ hΔ2 hD1) h h01 hsym _ hc
  have hhv : ∀ i j, i ≠ j → (h i j + h j i) / 2 = ‖v i - v j‖ ^ 2 / 4 := by
    intro i j hij
    have e1 := hvK i j hij
    rw [Matrix.of_apply] at e1
    rw [norm_sub_sq_real, hv.1 i, hv.1 j, e1, ← hsym i j, hh i j]
    ring
  have hsv : ∀ ω : Fin (P.samples (kvInst k z)) → (Fin (P.blockLen (kvInst k z)) → Bool),
      sdpValue ⟨P.nVert (kvInst k z), sgraph (P.nVert (kvInst k z)) P.Δ (dec hGP hok) ω⟩ v =
        edgeAvg ⟨P.nVert (kvInst k z), sgraph (P.nVert (kvInst k z)) P.Δ (dec hGP hok) ω⟩ h :=
    fun ω ↦ sdpValue_eq_edgeAvg
      ⟨P.nVert (kvInst k z), sgraph (P.nVert (kvInst k z)) P.Δ (dec hGP hok) ω⟩ v h hhv
  simp only [hsv]
  exact key

/-- **The witness at one degree**: for `d ≥ d₀`, a graph of maximum degree `d` and Max-Cut value
at most `s* + C log² d / d` with an SDP solution of value at least `c* - C'/d`. -/
theorem witness_at {C₁ C₀ : ℝ} {d₁ : ℕ} (hC₀ : 0 < C₀) (hd₁ : 30 ≤ d₁)
    (hS : ∀ d : ℕ, d₁ ≤ d → ∃ (b q R₀ : ℕ) (ε₀ : ℝ),
      0 < ε₀ ∧ q ≤ 2 ^ b ∧ -1 < 1 - 2 * (q : ℝ) / 2 ^ b ∧ 1 - 2 * (q : ℝ) / 2 ^ b < 0 ∧
      (1 - GW.rhoStar) / 2 - C₁ / d ≤ (1 - (1 - 2 * (q : ℝ) / 2 ^ b)) / 2 ∧
      ∀ R : ℕ, R₀ ≤ R →
        ((1 + |1 - 2 * (q : ℝ) / 2 ^ b|) / 2) ^ R ≤ 1 / (2 * ((d / 10 : ℕ) : ℝ) ^ 2) ∧
        ∀ G : UGInstance, GoodI R G → G.2.2.2 ≠ [] → ugValue G ≤ ε₀ →
          9 / 10 ≤ ((ProbComp.eval (redProg ⟨R, b, q, d / 10, d⟩ G)).toOuterMeasure
            (maxCutGap d ((1 - GW.rhoStar) / 2 - C₁ / d)
              (Real.arccos GW.rhoStar / Real.pi + C₁ * Real.log d ^ 2 / d)).no).toReal)
    (hY : ∀ D : ℕ, 1 ≤ D → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ Δ : ℕ, 10 * D ≤ Δ → ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (dec : Ω → Fin n × Fin n),
        (∀ a, frac (fun ω ↦ (dec ω).1 = a ∨ (dec ω).2 = a) ≤ 3 / n) →
        (∀ e, frac (fun ω ↦ dec ω = e) ≤ 1 / (n * D ^ 2)) →
        ∀ h : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ h i j ∧ h i j ≤ 1) → (∀ i j, h i j = h j i) →
        ∀ c : ℝ, c ≤ mean (fun ω ↦ h (dec ω).1 (dec ω).2) →
          9 / 10 ≤ frac fun ω : Fin (n * D) → Ω ↦
            c - C₀ / D ≤ edgeAvg ⟨n, sgraph n Δ dec ω⟩ h)
    {d : ℕ} (hd : d₁ ≤ d) :
    ∃ (H : Graph) (v : Fin H.1 → EuclideanSpace ℝ (Fin H.1)),
      MaxDegreeAtMost H d ∧ IsSDPSolution H.1 v ∧
      (1 - GW.rhoStar) / 2 - (C₁ + 20 * C₀ + 5) / d ≤ sdpValue H v ∧
      maxCutValue H ≤ Real.arccos GW.rhoStar / Real.pi + C₁ * Real.log d ^ 2 / d := by
  have hd30 : 30 ≤ d := hd₁.trans hd
  have hdr : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨b, q, R₀, ε₀, hε₀, hq, hρ1, hρ0, hρc, hR⟩ := hS d hd
  -- the parameters
  obtain ⟨T, hT8, hTd⟩ := exists_T_a d (by omega)
  have hΔs1 : 1 ≤ 4 * d := by omega
  have h4d : (4 : ℝ) / ((4 * d : ℕ) : ℝ) = 1 / d := by push_cast; field_simp
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 3 * (4 / ((4 * d : ℕ) : ℝ) + 1 / 2 ^ T) := ⟨_, rfl⟩
  have hδd : δ ≤ 6 / d := by
    rw [hδ, h4d]
    have e6 : (6 : ℝ) / d = 3 * (1 / d + 1 / d) := by ring
    linarith
  have hδ1 : δ ≤ 1 := hδd.trans (by rw [div_le_one hdr]; exact_mod_cast (show 6 ≤ d by omega))
  obtain ⟨a, ha⟩ : ∃ a : ℕ, 4 * d * tExp T (4 * d) ≤ 2 ^ a :=
    ⟨4 * d * tExp T (4 * d), Nat.lt_two_pow_self.le⟩
  obtain ⟨n₀, hn₀⟩ := hY (d / 10) (by omega)
  obtain ⟨k, hka, hkR, hkn, hkε⟩ := exists_k_large a R₀ n₀ hε₀
  have hk1 : 1 ≤ k := by omega
  have hs1 : 1 ≤ tExp T (4 * d) := by
    unfold tExp
    have : 0 < 4 ^ ((4 * d + 1) * T) := by positivity
    omega
  have h4a : 4 ≤ 2 ^ a := by
    refine le_trans ?_ ha
    have : 1 ≤ d * tExp T (4 * d) := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have h2k : 2 ^ k = 2 ^ (k - a) * 2 ^ a := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have hz1 : 1 ≤ 2 ^ (k - a) := Nat.one_le_two_pow
  have hz2 : 2 * 2 ^ (k - a) < 2 ^ k := by rw [h2k]; nlinarith
  have hz4 : 4 * 2 ^ (k - a) ≤ 2 ^ k := by rw [h2k]; nlinarith
  have hζ : 4 * ((2 ^ (k - a) : ℕ) : ℝ) / 2 ^ k * tExp T (4 * d) ≤ 1 / d := by
    have hz' : ((2 ^ (k - a) : ℕ) : ℝ) * 2 ^ a = 2 ^ k := by
      have := congrArg (fun m : ℕ ↦ (m : ℝ)) h2k
      push_cast at this ⊢
      linarith
    have ha' : (4 * d * tExp T (4 * d) : ℝ) ≤ 2 ^ a := by exact_mod_cast ha
    have h2k' : (0 : ℝ) < 2 ^ k := by positivity
    rw [div_mul_eq_mul_div, div_le_div_iff₀ h2k' hdr, ← hz']
    nlinarith [show (0 : ℝ) ≤ ((2 ^ (k - a) : ℕ) : ℝ) by positivity]
  -- the instance
  have hGood : GoodI (2 ^ k) (kvInst k (2 ^ (k - a))) := kvInst_good hk1 hz2
  have hcs : (kvInst k (2 ^ (k - a))).2.2.2 ≠ [] := kvInst_ne (by omega)
  have hval : ugValue (kvInst k (2 ^ (k - a))) ≤ ε₀ := (kvInst_value_le hk1 hz4).trans hkε
  have hok : Prm.ok ⟨2 ^ k, b, q, d / 10, d⟩ (kvInst k (2 ^ (k - a))) = true :=
    ok_of_good hGood hcs
  obtain ⟨hκ, hno⟩ := hR (2 ^ k) hkR
  have hNo := hno _ hGood hcs hval
  rw [show redProg ⟨2 ^ k, b, q, d / 10, d⟩ (kvInst k (2 ^ (k - a))) =
    (fun w ↦ reduce ⟨2 ^ k, b, q, d / 10, d⟩ ((kvInst k (2 ^ (k - a))), w)) <$>
      BitString.sampleList (Prm.coinCount ⟨2 ^ k, b, q, d / 10, d⟩ (kvInst k (2 ^ (k - a))))
    from rfl, prob_reduce hGood hok] at hNo
  -- the SDP side
  have hnn₀ : n₀ ≤ Prm.nVert ⟨2 ^ k, b, q, d / 10, d⟩ (kvInst k (2 ^ (k - a))) := by
    have h1 := two_pow_le_nVert (P := ⟨2 ^ k, b, q, d / 10, d⟩) hGood hok
    exact hkn.trans h1
  have hΔ2 : (d / 10) ^ 2 ≤ 2 ^ d := by
    have h1 := pow_two_ge (show 4 ≤ d by omega)
    have h2 : (d / 10) ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left (Nat.div_le_self d 10) 2
    exact h2.trans h1
  obtain ⟨v, hv, hYes⟩ := sdp_event (C₀ := C₀) (P := ⟨2 ^ k, b, q, d / 10, d⟩) hk1 hz2 hT8 hΔs1
    rfl hq hρ0.le hρ1.le hGood hok hcs hδ hδ1 (show 1 ≤ d / 10 by omega)
    (show 10 * (d / 10) ≤ d by omega) hΔ2 hκ hnn₀ hn₀
  -- both events
  simp only [sampledGraph_eq] at hNo
  obtain ⟨ω, hω₁, hω₂⟩ := exists_of_frac hNo hYes
  refine ⟨⟨Prm.nVert ⟨2 ^ k, b, q, d / 10, d⟩ (kvInst k (2 ^ (k - a))),
    sgraph _ d (dec hGood hok) ω⟩, v, hω₁.2, hv, le_trans ?_ hω₂, hω₁.1.1⟩
  have hinv : 1 / ((d / 10 : ℕ) : ℝ) ≤ 20 / d := inv_div_ten_le hd30
  have hCD : C₀ / ((d / 10 : ℕ) : ℝ) ≤ 20 * C₀ / d :=
    calc C₀ / ((d / 10 : ℕ) : ℝ) = C₀ * (1 / ((d / 10 : ℕ) : ℝ)) := by ring
      _ ≤ C₀ * (20 / d) := mul_le_mul_of_nonneg_left hinv hC₀.le
      _ = 20 * C₀ / d := by ring
  have h2d : (1 : ℝ) / 2 ^ d ≤ 1 / d := by
    apply one_div_le_one_div_of_le hdr
    exact_mod_cast Nat.lt_two_pow_self.le
  have hρP : Prm.rho ⟨2 ^ k, b, q, d / 10, d⟩ = 1 - 2 * (q : ℝ) / 2 ^ b := rfl
  have hPΔ : (2 : ℝ) ^ Prm.Δ ⟨2 ^ k, b, q, d / 10, d⟩ = 2 ^ d := rfl
  have hPD : ((Prm.D ⟨2 ^ k, b, q, d / 10, d⟩ : ℕ) : ℝ) = ((d / 10 : ℕ) : ℝ) := rfl
  rw [hρP, hPΔ, hPD]
  have e1 : (C₁ + 20 * C₀ + 5) / d = C₁ / d + 20 * C₀ / d + 4 / d + 1 / d := by ring
  have e2 : (δ + 4 * ((2 ^ (k - a) : ℕ) : ℝ) / 2 ^ k * tExp T (4 * d)) / 2 ≤ 4 / d := by
    have : (6 : ℝ) / d + 1 / d = 7 / d := by ring
    have h7 : (7 : ℝ) / d / 2 ≤ 4 / d := by
      rw [div_div, div_le_div_iff₀ (by positivity) hdr]; nlinarith
    linarith
  rw [e1]
  push_cast at e2 ⊢
  linarith

/-- The arithmetic of the integrality gap: with `B ≥ max(C₁, C₂, 1)` and `C = 4B/c*`, Max-Cut
value at most `s* + C₁ log² d/d` and SDP value at least `c* - C₂/d` give the three bounds. -/
theorem gap_arith {C₁ C₂ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) :
    ∃ (C : ℝ) (d₂ : ℕ), ∀ d : ℕ, d₂ ≤ d → ∀ {mc sv : ℝ},
      mc ≤ Real.arccos GW.rhoStar / Real.pi + C₁ * Real.log d ^ 2 / d →
      (1 - GW.rhoStar) / 2 - C₂ / d ≤ sv →
      (1 - GW.rhoStar) / 2 - C / d ≤ sv ∧
      mc ≤ Real.arccos GW.rhoStar / Real.pi + C * Real.log d ^ 2 / d ∧
      mc ≤ (alphaGW + C * Real.log d ^ 2 / d) * sv := by
  have hρ := GW.rhoStar_mem_window
  obtain ⟨cs, hcs_def⟩ : ∃ cs, cs = (1 - GW.rhoStar) / 2 := ⟨_, rfl⟩
  have hcs : 0 < cs := by rw [hcs_def]; linarith [hρ.2]
  have hcs1 : cs ≤ 1 := by rw [hcs_def]; linarith [hρ.1]
  have hss : Real.arccos GW.rhoStar / Real.pi = alphaGW * cs := by
    rw [GW.alphaGW_eq, gwRatio, ← hcs_def, div_mul_cancel₀ _ hcs.ne']
  have hα0 := GW.alphaGW_pos
  have hα1 := GW.alphaGW_lt_one
  obtain ⟨B, hB_def⟩ : ∃ B, B = max (max C₁ C₂) 1 := ⟨_, rfl⟩
  have hB : 1 ≤ B := hB_def ▸ le_max_right _ _
  have hB1 : C₁ ≤ B := hB_def ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hB2 : C₂ ≤ B := hB_def ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hCB : B ≤ 4 * B / cs := by rw [le_div_iff₀ hcs]; nlinarith
  refine ⟨4 * B / cs, max 3 (⌈4 * B / cs⌉₊ + 1), fun d hd mc sv hmc hsv ↦ ?_⟩
  rw [← hcs_def] at hsv ⊢
  rw [hss] at hmc ⊢
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast (le_max_left _ _).trans hd
  have hdB : 4 * B / cs < d := by
    have h1 : ⌈4 * B / cs⌉₊ + 1 ≤ d := (le_max_right _ _).trans hd
    have h2 : ((⌈4 * B / cs⌉₊ : ℕ) : ℝ) + 1 ≤ d := by exact_mod_cast h1
    linarith [Nat.le_ceil (4 * B / cs)]
  have hd0 : (0 : ℝ) < d := by linarith
  have hL : 1 ≤ Real.log d ^ 2 := by
    have : 1 < Real.log d :=
      KKMORobust.one_lt_log_three.trans_le (Real.log_le_log (by norm_num) hd3)
    exact one_le_pow₀ this.le
  obtain ⟨L, hL_def⟩ : ∃ L, L = Real.log d ^ 2 := ⟨_, rfl⟩
  rw [← hL_def] at hmc hL ⊢
  obtain ⟨u, hu_def⟩ : ∃ u, u = B / d := ⟨_, rfl⟩
  obtain ⟨v, hv_def⟩ : ∃ v, v = 4 * B / cs / d := ⟨_, rfl⟩
  have hu : 0 < u := by rw [hu_def]; exact div_pos (hC₁.trans_le hB1) hd0
  have hv : v < 1 := by rw [hv_def, div_lt_one hd0]; exact hdB
  have hv0 : 0 < v := by rw [hv_def]; positivity
  have huv : u ≤ v := by rw [hu_def, hv_def]; exact div_le_div_of_nonneg_right hCB hd0.le
  have hvcs : v * cs = 4 * u := by rw [hv_def, hu_def]; field_simp
  have hCv : 4 * B / cs * L / d = v * L := by rw [hv_def]; ring
  have hC₁v : C₁ * L / d = (C₁ / d) * L := by ring
  have hC₁u : C₁ / d ≤ u := hu_def ▸ div_le_div_of_nonneg_right hB1 hd0.le
  have hC₂u : C₂ / d ≤ u := hu_def ▸ div_le_div_of_nonneg_right hB2 hd0.le
  have hC₂0 : 0 < C₂ / d := div_pos hC₂ hd0
  have hC₂v : C₂ / d ≤ 4 * B / cs / d := hv_def ▸ hC₂u.trans huv
  have hmc' : mc ≤ alphaGW * cs + u * L := by
    rw [hC₁v] at hmc
    nlinarith
  rw [hCv]
  refine ⟨by linarith, by nlinarith, ?_⟩
  have hα' : 0 ≤ alphaGW + v * L := by positivity
  have h1 : (alphaGW + v * L) * (cs - u) ≤ (alphaGW + v * L) * sv :=
    mul_le_mul_of_nonneg_left (by linarith) hα'
  have hexp : (alphaGW + v * L) * (cs - u) =
      alphaGW * cs - alphaGW * u + 4 * u * L - v * u * L := by
    linear_combination L * hvcs
  have h2 : v * u * L ≤ u * L := by
    have := mul_le_mul_of_nonneg_right hv.le (mul_pos hu (by linarith : (0 : ℝ) < L)).le
    linarith
  have h3 : alphaGW * u ≤ u * L := by nlinarith
  have h4 : 0 ≤ u * L := by positivity
  linarith

/-- **Theorem 1.4** of [BGHKLMM26], from Theorem 7.1. -/
theorem integrality_gap (hMIS : RobustMIS) :
    ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d → ∀ ρ : ℝ, IsGWMinimizer ρ →
      ∃ (H : Graph) (v : Fin H.1 → EuclideanSpace ℝ (Fin H.1)),
        MaxDegreeAtMost H d ∧ IsSDPSolution H.1 v ∧
        (1 - ρ) / 2 - C / d ≤ sdpValue H v ∧
        maxCutValue H ≤ Real.arccos ρ / Real.pi + C * Real.log d ^ 2 / d ∧
        maxCutValue H ≤ (alphaGW + C * Real.log d ^ 2 / d) * sdpValue H v := by
  obtain ⟨C₁, d₁, hC₁, hd₁, hS⟩ := sound_at hMIS
  obtain ⟨C₀, hC₀, hY⟩ := sparsify_yes_score
  obtain ⟨C, d₂, hC⟩ := gap_arith hC₁ (show 0 < C₁ + 20 * C₀ + 5 by positivity)
  refine ⟨C, max d₁ d₂, fun d hd ρ hρ ↦ ?_⟩
  have hρ' : ρ = GW.rhoStar := GW.exists_unique_isGWMinimizer.unique hρ GW.isGWMinimizer_rhoStar
  subst hρ'
  obtain ⟨H, v, hdeg, hv, hsdp, hcut⟩ := witness_at hC₀ hd₁ hS hY (le_of_max_le_left hd)
  obtain ⟨h1, h2, h3⟩ := hC d (le_of_max_le_right hd) hcut hsdp
  exact ⟨H, v, hdeg, hv, h1, h2, h3⟩

end BGHKLMM26.IntGap
