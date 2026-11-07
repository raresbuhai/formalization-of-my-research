module

public import BHSV25.BK.Sound
public import BHSV25.BK.Machine

/-!
# Bansal and Khot's theorem from the Unique Games Conjecture

The assembly (`BHSV25/BK/README.md`, Section 5): given `ε, γ ≤ 1/8` and `η > 0`, the parameters
`M = ⌈2/ε⌉ + ⌈4/γ⌉ + 2`, `(K, τ, t)` from It Ain't Over Till It's Over (`BHSV25.BK.ItAintOver`)
for `γ / 8`, `ε₁` from the decoding (`BHSV25.BK.few_bad`), `δ = min(ε₀, ε₁, ε / (2(t+1)))` and `R`
from the Unique Games Conjecture for `δ`. The reduction `BHSV25.BK.Prm.reduce` with `k₀ = ⌈1/η⌉ + 1`
copies maps the yes-instances of `ugGap R δ δ` to yes-instances of `bkGap' ε γ η`
(`BHSV25.BK.Prm.complete`) and the no-instances to no-instances (`BHSV25.BK.Prm.sound`); with
`R = 0` there are no yes-instances and a constant map does. `NPHard.trans` concludes
(`BHSV25.BK.bansalKhot_of`).
-/

@[expose] public section

namespace BHSV25.BK

open Finset UniqueGames Cslib.Complexity OAI.MaxCutGames.Foundations.Hastad
  OAI.OptimalMaxCut.Analytic Turing.MultiTapeTM

/-- The fixed no-instance: `k₀` disjoint cliques on `s > 1/γ` vertices. -/
theorem cliques_no {ε γ η : ℝ} (hγε : γ ≤ 1 / 2 - ε) {k₀ s : ℕ}
    (hk : 1 ≤ η * k₀) (hs : 1 < γ * s) : copies (clique s) k₀ ∈ (bkGap' ε γ η).no := by
  have hk0 : 0 < k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h | h
    · rw [h] at hk; simp at hk; linarith
    · exact h
  refine ⟨copies_maxDeg _ hk, hγε, fun I hI ↦ ?_⟩
  obtain ⟨S, hS, hIS⟩ := copies_indep (clique s) hk0 I hI
  have h1 := clique_indep S hS
  have h2 : (I.card : ℝ) ≤ k₀ := by
    have : I.card ≤ k₀ := by nlinarith
    exact_mod_cast this
  have hk0' : (0 : ℝ) < k₀ := by exact_mod_cast hk0
  calc (I.card : ℝ) ≤ k₀ := h2
    _ = k₀ * 1 := (mul_one _).symm
    _ < k₀ * (γ * s) := mul_lt_mul_of_pos_left hs hk0'
    _ = γ * (copies (clique s) k₀).1 := by simp [clique]; ring

theorem min_left_eq {R : ℕ} {G : UGInstance} (hG : Good R G) (hL : Prm.ldeg G.2.2.2 ≠ 0) :
    min G.1 G.2.2.2.length = G.1 := by
  have hcs : G.2.2.2 ≠ [] := by
    intro h; apply hL; simp [Prm.ldeg, nbrs, h]
  obtain ⟨D, hD, -, -, hcard⟩ := exists_leftDeg hG hcs
  rw [hcard]
  exact min_eq_left (Nat.le_mul_of_pos_right _ hD)

/-- Instances with `R = 0` labels have value `0`. -/
theorem ugValue_le_zero_of_R_zero {G : UGInstance} (hv : UGValid G) (hR : G.2.2.1 = 0) :
    ugValue G ≤ 0 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨σ, τ, hopt⟩ := exists_opt_labeling G h
  rcases Nat.eq_zero_or_pos G.1 with hm | hm
  · have hcs : G.2.2.2 = [] := by
      rcases List.eq_nil_or_concat G.2.2.2 with h' | ⟨l, c, h'⟩
      · exact h'
      · have := (hv c (by rw [h']; simp)).1
        omega
    rw [hopt, hcs] at h
    simp at h
  · have := (σ ⟨0, hm⟩).2
    omega

/-- **Bansal and Khot's theorem**, from the Unique Games Conjecture and It Ain't Over Till It's
Over. -/
theorem bansalKhot_of (hUGC : UGC) (hAIO : ItAintOver) : BansalKhot' := by
  obtain ⟨ε₀', hε₀', hε₀'h, hUG⟩ := hUGC
  refine ⟨1 / 8, by norm_num, fun ε γ η hε hε8 hγ hγ8 hη ↦ ?_⟩
  have hγε : γ ≤ 1 / 2 - ε := by linarith
  -- the parameters
  set M : ℕ := ⌈2 / ε⌉₊ + ⌈4 / γ⌉₊ + 2 with hMdef
  have hM2 : 2 ≤ M := by omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMε : 1 / (M : ℝ) ≤ ε / 2 := by
    have : 2 / ε ≤ (M : ℝ) := by
      calc 2 / ε ≤ ⌈2 / ε⌉₊ := Nat.le_ceil _
        _ ≤ M := by rw [hMdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈4 / γ⌉₊]
    rw [div_le_iff₀ hMr]
    rw [div_le_iff₀ hε] at this
    linarith
  have hMγ : 1 / (M : ℝ) ≤ γ / 4 := by
    have : 4 / γ ≤ (M : ℝ) := by
      calc 4 / γ ≤ ⌈4 / γ⌉₊ := Nat.le_ceil _
        _ ≤ M := by rw [hMdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈2 / ε⌉₊]
    rw [div_le_iff₀ hMr]
    rw [div_le_iff₀ hγ] at this
    linarith
  obtain ⟨K, τ, hτ, t, hA⟩ := hAIO M hM2 (γ / 8) (by positivity)
  obtain ⟨ε₁, hε₁, hfew⟩ := few_bad K hτ (ν := γ / 8) (by positivity)
  set δ : ℝ := min (min ε₀' ε₁) (ε / (2 * (t + 1))) with hδdef
  have hδ : 0 < δ := lt_min (lt_min hε₀' hε₁) (by positivity)
  have hδ0 : δ ≤ ε₀' := (min_le_left _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ ε₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hδt : t * δ ≤ ε / 2 := by
    have h1 : δ ≤ ε / (2 * (t + 1)) := min_le_right _ _
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  obtain ⟨R, hR⟩ := hUG δ hδ hδ0
  set k₀ : ℕ := ⌈1 / η⌉₊ + 1 with hk₀def
  set s : ℕ := ⌈1 / γ⌉₊ + 1 with hsdef
  have hk : 1 ≤ η * k₀ := by
    have : 1 / η ≤ (k₀ : ℝ) := by
      calc 1 / η ≤ ⌈1 / η⌉₊ := Nat.le_ceil _
        _ ≤ k₀ := by rw [hk₀def]; push_cast; linarith
    rw [div_le_iff₀ hη] at this
    linarith
  have hs : 1 < γ * s := by
    have : 1 / γ < (s : ℝ) := by
      calc 1 / γ ≤ ⌈1 / γ⌉₊ := Nat.le_ceil _
        _ < s := by rw [hsdef]; push_cast; linarith
    rw [div_lt_iff₀ hγ] at this
    linarith
  have hk0 : 0 < k₀ := by omega
  have hno₀ := cliques_no hγε hk hs
  by_cases hR0 : R = 0
  · -- no labels: no yes-instances
    subst hR0
    refine hR.trans ⟨fun _ ↦ copies (clique s) k₀, ComputableInPolyTime.const _, ?_,
      fun _ _ ↦ hno₀⟩
    rintro G ⟨hyes, hv, hR, -, -⟩
    have := ugValue_le_zero_of_R_zero hv hR
    simp only [PromiseProblem.mem_yes_gapMax] at hyes
    have : δ ≤ 1 / 2 := hδ0.trans hε₀'h
    linarith
  let P : Prm := ⟨R, t, M, k₀, s⟩
  refine hR.trans ⟨P.reduce, P.reduce_polytime, ?_, ?_⟩
  · -- yes-instances
    rintro G ⟨hyes, hG⟩
    simp only [PromiseProblem.mem_yes_gapMax] at hyes
    have hG' : Good P.R G := hG
    have hpos : 0 < ugValue G := by linarith [hδ0.trans hε₀'h]
    have hL : Prm.ldeg G.2.2.2 ≠ 0 := by
      intro hL
      obtain ⟨σ, τ, hopt⟩ := exists_opt_labeling G hpos
      have hcs : G.2.2.2 ≠ [] := by
        intro hcs; rw [hopt, hcs] at hpos; simp at hpos
      obtain ⟨D, hD, hm, hlen, -⟩ := exists_leftDeg hG' hcs
      have := hlen 0 hm
      unfold Prm.ldeg at hL
      omega
    obtain ⟨I, J, hIJ, hI, hJ, hIc, hJc⟩ :=
      P.complete hG' hL (by positivity) (by linarith [hδ0.trans hε₀'h]) hyes
    obtain ⟨I', J', hd, hI', hJ', hIc', hJc'⟩ := copies_yes _ k₀ hIJ hI hJ
    have hred : P.reduce G = copies (P.baseGraph G.2.2.2 G.1 (Prm.ldeg G.2.2.2)) k₀ := by
      simp only [Prm.reduce, hL, ↓reduceIte, min_left_eq hG' hL]; rfl
    rw [hred]
    refine ⟨copies_maxDeg _ hk, I', J', hd, hI', hJ', ?_, ?_⟩
    · rw [hIc']
      push_cast
      have hb : (1 / 2 - ε) * (P.nV G.1 (Prm.ldeg G.2.2.2) : ℝ) ≤ I.card := by
        refine le_trans ?_ hIc
        have hN : (0 : ℝ) ≤ P.nV G.1 (Prm.ldeg G.2.2.2) := Nat.cast_nonneg _
        have : (1 / 2 - ε) ≤ (1 - P.t * δ - 1 / P.M) / 2 := by
          change (1 / 2 - ε) ≤ (1 - t * δ - 1 / (M : ℝ)) / 2
          linarith
        nlinarith
      have hk0' : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg _
      calc (1 / 2 - ε) * ((k₀ : ℝ) * (P.nV G.1 (Prm.ldeg G.2.2.2) : ℝ)) =
          k₀ * ((1 / 2 - ε) * (P.nV G.1 (Prm.ldeg G.2.2.2) : ℝ)) := by ring
        _ ≤ k₀ * I.card := mul_le_mul_of_nonneg_left hb hk0'
    · rw [hJc']
      push_cast
      have hb : (1 / 2 - ε) * (P.nV G.1 (Prm.ldeg G.2.2.2) : ℝ) ≤ J.card := by
        refine le_trans ?_ hJc
        have hN : (0 : ℝ) ≤ P.nV G.1 (Prm.ldeg G.2.2.2) := Nat.cast_nonneg _
        have : (1 / 2 - ε) ≤ (1 - P.t * δ - 1 / P.M) / 2 := by
          change (1 / 2 - ε) ≤ (1 - t * δ - 1 / (M : ℝ)) / 2
          linarith
        nlinarith
      have hk0' : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg _
      calc (1 / 2 - ε) * ((k₀ : ℝ) * (P.nV G.1 (Prm.ldeg G.2.2.2) : ℝ)) =
          k₀ * ((1 / 2 - ε) * (P.nV G.1 (Prm.ldeg G.2.2.2) : ℝ)) := by ring
        _ ≤ k₀ * J.card := mul_le_mul_of_nonneg_left hb hk0'
  · -- no-instances
    rintro G ⟨⟨hno, -⟩, hG⟩
    have hG' : Good P.R G := hG
    by_cases hL : Prm.ldeg G.2.2.2 = 0
    · have hred : P.reduce G = copies (clique s) k₀ := by
        simp only [Prm.reduce, hL, ↓reduceIte]; rfl
      rw [hred]
      exact hno₀
    have hred : P.reduce G = copies (P.baseGraph G.2.2.2 G.1 (Prm.ldeg G.2.2.2)) k₀ := by
      simp only [Prm.reduce, hL, ↓reduceIte, min_left_eq hG' hL]; rfl
    rw [hred]
    refine ⟨copies_maxDeg _ hk, hγε, fun I hI ↦ ?_⟩
    obtain ⟨S, hS, hIS⟩ := copies_indep _ hk0 I hI
    have hSc := P.sound hG' hL (Nat.pos_of_ne_zero hR0) (show 0 < M by omega) hMγ
      (fun g hg0 hg1 hg2 ↦ hA R g hg0 hg1 hg2) (hfew δ hδ hδ1 R G hG hno) S hS
    have hk0' : (0 : ℝ) < k₀ := by exact_mod_cast hk0
    calc (I.card : ℝ) ≤ k₀ * S.card := by exact_mod_cast hIS
      _ < k₀ * (γ * P.nV G.1 (Prm.ldeg G.2.2.2)) := mul_lt_mul_of_pos_left hSc hk0'
      _ = γ * (copies (P.baseGraph G.2.2.2 G.1 (Prm.ldeg G.2.2.2)) k₀).1 := by
          push_cast; ring

end BHSV25.BK
