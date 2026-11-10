module

public import BHSV25.Alg.Partition
public import BHSV25.Alg.GridCluster
public import BHSV25.Net.GSMachine
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Recovering partitions with a grid of centers

[BHSV25, Theorem 5.1] for regular graphs, with a net of constant precision `η` and the grid of
centers of [BHSV25, Lemma 5.4] (`BHSV25.Alg.exists_good_grid`). Let `χ` be a partition of the
vertices of a regular graph with at most one eigenvalue above `L ∈ (0, 1)`, with `m` parts of at
least `c n` vertices, weight at most `ε₀ n` inside the parts, and a model whose rows are
`α`-separated; let `0 < θ < τ` with `2 τ² / c ≤ α² / 2`, and let `U` contain a vector within `η`
of every vector of norm at most `1` in the span of the eigenvectors with `|μ| ≥ θ`. Then for some
`m`-tuple of vectors of `U` and some grid of centers the clusters of `BHSV25.Alg.clustersC` agree
with `χ` on all but `(512 m⁴ (ε₀ / L + L) / (c (τ - θ)² α²) + 512 m² η² / α²) · n` vertices.

The proof follows the paper's Lemma 5.4. The values `V_(r,a) = z_(r,a) / √|V_a|` of the
eigenvectors of the symmetrized model on the parts are at most `1 / √(c n)`, so the grid of
spacing `1 / (S ⌊√n⌋)` and range `K / (S ⌊√n⌋)` has a center within `√ρ` of the values of every
part, `ρ = α² / (128 m n)`, when `128 m² ≤ α² S²` and `S² ≤ c (K - 1)²`. A vertex is good when
its coordinates on the net vectors are within `ρ` of the values of its part; good vertices are
nearer to the center of their part than to the others (`BHSV25.Alg.sum_sq_lt_of_center`), as the
values of different parts are `α² / (4 m n) = 32 ρ` apart (Lemma 5.3). The others are few, by
Markov's inequality: the net's error contributes `512 m² η² / α²` and the eigenspace
approximation (Lemma 5.2) the rest.
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Matrix Finset Spectral

/-- **Good points are nearest to their own center**: if `u` is within `ρ` of the values `v` of
its part, the centers `w` and `w'` are within `ρ` of the values `v` and `v'`, and the values are
`σ`-separated with `16 ρ < σ`, then `u` is nearer to `w` than to `w'`. -/
theorem sum_sq_lt_of_center {R : Type*} [Fintype R] (u v w v' w' : R → ℝ) {ρ σ : ℝ}
    (hρσ : 16 * ρ < σ) (hu : ∑ r, (u r - v r) ^ 2 ≤ ρ) (hw : ∑ r, (w r - v r) ^ 2 ≤ ρ)
    (hw' : ∑ r, (w' r - v' r) ^ 2 ≤ ρ) (hsep : σ ≤ ∑ r, (v r - v' r) ^ 2) :
    ∑ r, (u r - w r) ^ 2 < ∑ r, (u r - w' r) ^ 2 := by
  have h1 : ∑ r, (u r - w r) ^ 2 ≤ 4 * ρ := by
    have := sum_sq_sub_le (fun r ↦ u r - v r) (fun r ↦ w r - v r)
    have e : ∀ r, u r - v r - (w r - v r) = u r - w r := fun r ↦ by ring
    simp only [e] at this
    linarith
  have h2 : σ / 2 - 4 * ρ ≤ ∑ r, (u r - w' r) ^ 2 := by
    have hq := sum_sq_sub_le (fun r ↦ u r - v r) (fun r ↦ w' r - v' r)
    have hpt : ∀ r, (v r - v' r) ^ 2 / 2 - (u r - v r - (w' r - v' r)) ^ 2 ≤ (u r - w' r) ^ 2 := by
      intro r
      have e : u r - w' r = (v r - v' r) + (u r - v r - (w' r - v' r)) := by ring
      rw [e]
      nlinarith [sq_nonneg (v r - v' r + 2 * (u r - v r - (w' r - v' r)))]
    have hsum := sum_le_sum fun r (_ : r ∈ univ) ↦ hpt r
    rw [sum_sub_distrib, ← sum_div] at hsum
    linarith
  linarith

section Grid

variable {G : Graph} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The values of the eigenvectors on the parts are at most `1 / √|V_a|`. -/
theorem abs_partValue_le (χ : Fin G.1 → ι) (τ : ℝ) (r a : ι) :
    |partValue χ τ r a| ≤ 1 / Real.sqrt (part G χ a).card := by
  unfold partValue
  split_ifs
  · rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    have h1 := eigVec_dotProduct_self (G := G) χ r
    have h2 : eigVec χ r a ^ 2 ≤ eigVec χ r ⬝ᵥ eigVec χ r := by
      rw [dotProduct]
      have := single_le_sum (f := fun b ↦ eigVec χ r b * eigVec χ r b)
        (fun b _ ↦ mul_self_nonneg _) (mem_univ a)
      simpa [sq] using this
    rw [h1] at h2
    exact (sq_le_one_iff_abs_le_one _).1 h2
  · simp only [abs_zero]
    positivity

/-- `⌊√n⌋` is between `√n / 2` and `√n`. -/
theorem sqrt_bounds {n : ℕ} (hn : 0 < n) :
    Real.sqrt n / 2 ≤ (Nat.sqrt n : ℝ) ∧ (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
  have hle : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast Nat.sqrt_le' n
  refine ⟨?_, hle⟩
  have hlt : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' n
  have hpos : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.2 hn
  have h1 : Real.sqrt n < Nat.sqrt n + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact hlt
  have h2 : (1 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hpos
  linarith

/-- A point of the grid `{(t - K) / (S R) : t ≤ 2K}` within `1 / (2 S R)` of a value `v` with
`|v S R| ≤ K - 1`. -/
theorem exists_grid_center {S K R : ℕ} (hS0 : (0 : ℝ) < S) (hR0 : (0 : ℝ) < R) {v : ℝ}
    (hv : |v * S * R| ≤ (K : ℝ) - 1) :
    ∃ t : ℕ, t < 2 * K + 1 ∧ |((t : ℝ) - K) / (S * R) - v| ≤ 1 / (2 * (S * R)) := by
  set z : ℤ := round (v * S * R) with hz
  have h1 : |(z : ℝ) - v * S * R| ≤ 1 / 2 := by rw [abs_sub_comm]; exact abs_sub_round _
  have h2 : |(z : ℝ)| < (K : ℝ) := by
    have := abs_add_le ((z : ℝ) - v * S * R) (v * S * R)
    simp only [sub_add_cancel] at this
    linarith
  have h3 : |z| < (K : ℤ) := by
    have : ((|z| : ℤ) : ℝ) < ((K : ℤ) : ℝ) := by rw [Int.cast_abs]; exact_mod_cast h2
    exact_mod_cast this
  have hz0 : 0 ≤ z + K := by have := (abs_lt.1 h3).1; omega
  refine ⟨(z + K).toNat, by have := (abs_lt.1 h3).2; omega, ?_⟩
  have h4 : (((z + K).toNat : ℕ) : ℝ) = (z : ℝ) + K := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hz0]; push_cast; ring
  rw [h4, add_sub_cancel_right]
  have hSR : (0 : ℝ) < S * R := mul_pos hS0 hR0
  have e1 : (z : ℝ) / (S * R) - v = ((z : ℝ) - v * S * R) / (S * R) := by field_simp
  rw [e1, abs_div, abs_of_pos hSR, div_le_div_iff₀ hSR (by positivity)]
  nlinarith

/-- **Good vertices are clustered right**: a vertex within `ρ` of the values of its part is
nearest to the center of its part, when the centers are within `ρ` of the values of their parts
and the values of different parts are `32 ρ` apart. -/
theorem clusterIdxC_good {m n : ℕ} {ι : Type*} [Fintype ι] (e : ι ≃ Fin m)
    (us : Fin m → List ℚ) (cs : List (List ℚ)) (hcs : cs.length = m) (Ur : ι → Fin n → ℝ)
    (hUr : ∀ r y, Ur r y = (((us (e r)).getD y 0 : ℚ) : ℝ)) (C V : ι → ι → ℝ)
    (hC : ∀ a j : Fin m, (((cs.getD a []).getD j 0 : ℚ) : ℝ) = C (e.symm j) (e.symm a))
    {ρ : ℝ} (hρ : 0 < ρ) (hCclose : ∀ a, ∑ r, (C r a - V r a) ^ 2 ≤ ρ)
    (hsepV : ∀ a b, a ≠ b → 32 * ρ ≤ ∑ r, (V r a - V r b) ^ 2) (a : ι) (y : Fin n)
    (hy : ∑ r, (Ur r y - V r a) ^ 2 ≤ ρ) :
    clusterIdxC (List.ofFn us) cs y = e a := by
  have hdist : ∀ b : Fin m, ((sqDistC (List.ofFn us) y (cs.getD b []) : ℚ) : ℝ) =
      ∑ r, (Ur r y - C r (e.symm b)) ^ 2 := by
    intro b
    rw [sqDistC_ofFn_cast]
    rw [← Equiv.sum_comp e.symm (fun r ↦ (Ur r y - C r (e.symm b)) ^ 2)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hC b j, hUr, Equiv.apply_symm_apply]
  refine clusterIdxC_eq _ _ _ (by rw [hcs]; exact (e a).2) fun b hb hba ↦ ?_
  rw [hcs] at hb
  rw [← Rat.cast_lt (K := ℝ)]
  have hd1 := hdist (e a)
  have hd2 := hdist ⟨b, hb⟩
  rw [Equiv.symm_apply_apply] at hd1
  rw [hd1, hd2]
  set b' := e.symm ⟨b, hb⟩ with hb'def
  have hb'ne : a ≠ b' := by
    intro hcon
    apply hba
    have : e b' = e a := by rw [hcon]
    rw [hb'def, Equiv.apply_symm_apply] at this
    exact congrArg Fin.val this
  have key := sum_sq_lt_of_center (fun r ↦ Ur r y) (fun r ↦ V r a) (fun r ↦ C r a)
    (fun r ↦ V r b') (fun r ↦ C r b') (σ := 32 * ρ) (by linarith) hy (hCclose a) (hCclose b')
    (hsepV a b' hb'ne)
  exact key

open Classical in
/-- **Theorem 5.1 with a grid of centers.** -/
theorem exists_good_grid {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0)
    {m : ℕ} (χ : Fin G.1 → ι) (e : ι ≃ Fin m) {c α L ε₀ θ τ η : ℝ}
    (hn : 0 < G.1) (hc : 0 < c) (hsize : ∀ a, c * G.1 ≤ (part G χ a).card)
    (hα : 0 < α) (hsep : ∀ a b, a ≠ b → α ^ 2 ≤ ∑ j, (pmodel G χ a j - pmodel G χ b j) ^ 2)
    (hL0 : 0 < L) (hL1 : L < 1) (hexp : G.numEigGT L ≤ 1) (hint : intWt G χ ≤ ε₀ * G.1)
    (hθτ : θ < τ) (hτ : τ ^ 2 * (2 / c) ≤ α ^ 2 / 2) (U : List (List ℚ))
    (hnet : ∀ w : Fin G.1 → ℝ, w ⬝ᵥ w ≤ 1 → G.InEigSpan (fun μ ↦ θ ≤ |μ|) w →
      ∃ u ∈ U, (Net.ratVec G.1 u - w) ⬝ᵥ (Net.ratVec G.1 u - w) ≤ η ^ 2)
    {S K : ℕ} (hS : 128 * (m : ℝ) ^ 2 ≤ α ^ 2 * (S : ℝ) ^ 2) (hK1 : 1 ≤ K)
    (hK : (S : ℝ) ^ 2 ≤ c * ((K : ℝ) - 1) ^ 2) :
    ∃ us : Fin m → List ℚ, (∀ j, us j ∈ U) ∧ ∃ ts : Fin (m * m) → Fin (2 * K + 1),
      ((univ.filter fun y : Fin G.1 ↦ clusterIdxC (List.ofFn us)
          (gridCenters m S K (Nat.sqrt G.1) (List.ofFn fun k ↦ (ts k : ℕ))) y ≠ e (χ y)).card :
          ℝ) ≤
        (512 * m ^ 4 * (ε₀ / L + L) / (c * (τ - θ) ^ 2 * α ^ 2) + 512 * m ^ 2 * η ^ 2 / α ^ 2) *
          G.1 := by
  classical
  have hm : Fintype.card ι = m := by simpa using Fintype.card_congr e
  have hnR : (0 : ℝ) < G.1 := by exact_mod_cast hn
  have hpos : ∀ a, (0 : ℝ) < (part G χ a).card := fun a ↦
    lt_of_lt_of_le (by positivity) (hsize a)
  have hne : ∀ a, (part G χ a).Nonempty := fun a ↦ card_pos.1 (by exact_mod_cast hpos a)
  have hη : 0 < τ - θ := sub_pos.2 hθτ
  set E := 512 * (m : ℝ) ^ 4 * (ε₀ / L + L) / (c * (τ - θ) ^ 2 * α ^ 2) with hEdef
  set F := 512 * (m : ℝ) ^ 2 * η ^ 2 / α ^ 2 with hFdef
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : IsEmpty (Fin G.1) := ⟨fun y ↦ hι.false (χ y)⟩
    have h0 : G.1 = 0 := by simpa using this
    omega
  have hmpos : (0 : ℝ) < m := by
    rw [← hm]
    exact_mod_cast Fintype.card_pos
  -- the net vectors
  choose u hu hud using fun r ↦ hnet (netTarget χ θ τ r) (netTarget_dotProduct_le χ hne θ τ r)
    (netTarget_inEigSpan χ θ τ r)
  set Ur : ι → Fin G.1 → ℝ := fun r ↦ Net.ratVec G.1 (u r) with hUr
  set W := netTarget (G := G) χ θ τ with hW
  set V := partValue (G := G) χ τ with hV
  set ρ : ℝ := α ^ 2 / (128 * m * G.1) with hρ
  have hρpos : 0 < ρ := by positivity
  -- vertices spoiled by the net: few
  set B1 := univ.filter fun y ↦ ρ / 4 < ∑ r, (Ur r y - W r y) ^ 2 with hB1
  have hB1c : (B1.card : ℝ) ≤ F * G.1 := by
    have hmk := card_lt_le_sum (fun y ↦ ∑ r, (Ur r y - W r y) ^ 2)
      (fun y ↦ sum_nonneg fun r _ ↦ sq_nonneg _) (ρ / 4)
    rw [← hB1, sum_comm] at hmk
    have hsum : ∑ r, ∑ y, (Ur r y - W r y) ^ 2 ≤ m * η ^ 2 := by
      calc ∑ r, ∑ y, (Ur r y - W r y) ^ 2 ≤ ∑ _r : ι, η ^ 2 := by
            refine sum_le_sum fun r _ ↦ ?_
            have := hud r
            simp only [dotProduct, Pi.sub_apply] at this
            simpa only [sq] using this
        _ = m * η ^ 2 := by rw [sum_const, card_univ, hm, nsmul_eq_mul]
    have h1 := hmk.trans hsum
    have h2 : (m : ℝ) * η ^ 2 = F * G.1 * (ρ / 4) := by
      rw [hFdef, hρ]
      field_simp
      ring
    rw [h2] at h1
    exact le_of_mul_le_mul_right h1 (by positivity)
  -- vertices far from the values of their parts: few
  set B2 := univ.filter fun y ↦ ρ / 4 < ∑ r, (W r y - V r (χ y)) ^ 2 with hB2
  have hB2c : (B2.card : ℝ) ≤ E * G.1 := by
    have hmk := card_lt_le_sum (fun y ↦ ∑ r, (W r y - V r (χ y)) ^ 2)
      (fun y ↦ sum_nonneg fun r _ ↦ sq_nonneg _) (ρ / 4)
    rw [← hB2, sum_comm] at hmk
    have hsum : ∑ r, ∑ y, (W r y - V r (χ y)) ^ 2 ≤
        m * (m ^ 2 * (ε₀ / L + L) / (c * (τ - θ) ^ 2)) := by
      calc ∑ r, ∑ y, (W r y - V r (χ y)) ^ 2 ≤
            ∑ _r : ι, (m : ℝ) ^ 2 * (ε₀ / L + L) / (c * (τ - θ) ^ 2) := by
            refine sum_le_sum fun r _ ↦ ?_
            have := sum_netTarget_sub_le h hd χ hc hsize hn hL0 hL1 hexp hint hθτ r
            rw [hm] at this
            exact this
        _ = m * (m ^ 2 * (ε₀ / L + L) / (c * (τ - θ) ^ 2)) := by
            rw [sum_const, card_univ, hm, nsmul_eq_mul]
    have h1 := hmk.trans hsum
    have h2 : (m : ℝ) * (m ^ 2 * (ε₀ / L + L) / (c * (τ - θ) ^ 2)) = E * G.1 * (ρ / 4) := by
      rw [hEdef, hρ]
      field_simp
      ring
    rw [h2] at h1
    exact le_of_mul_le_mul_right h1 (by positivity)
  -- good vertices
  have hgood : ∀ y, y ∉ B1 → y ∉ B2 → ∑ r, (Ur r y - V r (χ y)) ^ 2 ≤ ρ := by
    intro y hy1 hy2
    have h1 : ¬ ρ / 4 < ∑ r, (Ur r y - W r y) ^ 2 :=
      fun hlt ↦ hy1 (mem_filter.2 ⟨mem_univ _, hlt⟩)
    have h2 : ¬ ρ / 4 < ∑ r, (W r y - V r (χ y)) ^ 2 :=
      fun hlt ↦ hy2 (mem_filter.2 ⟨mem_univ _, hlt⟩)
    push Not at h1 h2
    have h3 := sum_sq_sub_le (fun r ↦ Ur r y - W r y) (fun r ↦ V r (χ y) - W r y)
    have e3 : ∀ r, Ur r y - W r y - (V r (χ y) - W r y) = Ur r y - V r (χ y) := fun r ↦ by ring
    simp only [e3] at h3
    have e4 : ∑ r, (V r (χ y) - W r y) ^ 2 = ∑ r, (W r y - V r (χ y)) ^ 2 :=
      sum_congr rfl fun r _ ↦ by ring
    rw [e4] at h3
    linarith
  -- the grid
  set R := Nat.sqrt G.1 with hR
  obtain ⟨hR1, hR2⟩ := sqrt_bounds hn
  have hRpos : (0 : ℝ) < R := by have := Real.sqrt_pos.2 hnR; linarith
  have hS0 : (0 : ℝ) < S := by
    have : (0 : ℝ) < α ^ 2 * (S : ℝ) ^ 2 := lt_of_lt_of_le (by positivity) hS
    have hS' : (S : ℝ) ≠ 0 := by intro h0; rw [h0] at this; simp at this
    exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hS')
  have hVb : ∀ r a, |V r a * S * R| ≤ (K : ℝ) - 1 := by
    intro r a
    have h1 := abs_partValue_le (G := G) χ τ r a
    have h2 : Real.sqrt (c * G.1) ≤ Real.sqrt (part G χ a).card := Real.sqrt_le_sqrt (hsize a)
    have hcn : 0 < Real.sqrt (c * G.1) := Real.sqrt_pos.2 (by positivity)
    have h3 : |V r a| ≤ 1 / Real.sqrt (c * G.1) :=
      h1.trans (one_div_le_one_div_of_le hcn h2)
    rw [abs_mul, abs_mul, abs_of_pos hS0, abs_of_pos hRpos]
    have hK' : (S : ℝ) ≤ Real.sqrt c * ((K : ℝ) - 1) := by
      have hK0 : (0 : ℝ) ≤ (K : ℝ) - 1 := by
        have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
        linarith
      rw [← Real.sqrt_sq hS0.le, ← Real.sqrt_sq hK0, ← Real.sqrt_mul hc.le]
      exact Real.sqrt_le_sqrt hK
    have hsc : Real.sqrt (c * G.1) = Real.sqrt c * Real.sqrt G.1 := Real.sqrt_mul hc.le _
    calc |V r a| * S * R ≤ 1 / Real.sqrt (c * G.1) * S * Real.sqrt G.1 := by gcongr
      _ = S / Real.sqrt c := by
          rw [hsc]
          have : Real.sqrt G.1 ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
          field_simp
      _ ≤ (K : ℝ) - 1 := by
          rw [div_le_iff₀ (Real.sqrt_pos.2 hc)]
          linarith
  choose tN htNlt htNclose using fun r a ↦ exists_grid_center hS0 hRpos (hVb r a)
  set ts : Fin (m * m) → Fin (2 * K + 1) := fun k ↦
    ⟨tN (e.symm (finProdFinEquiv.symm k).2) (e.symm (finProdFinEquiv.symm k).1),
      htNlt _ _⟩ with hts
  set C : ι → ι → ℝ := fun r a ↦ ((tN r a : ℝ) - K) / (S * R) with hC
  have hCval : ∀ a j : Fin m, (((gridCenters m S K R (List.ofFn fun k ↦ (ts k : ℕ))).getD a
      []).getD j 0 : ℝ) = C (e.symm j) (e.symm a) := by
    intro a j
    rw [getD_gridCenters _ a.2 j.2]
    have hidx : (a : ℕ) * m + j = (finProdFinEquiv (a, j) : ℕ) := by
      rw [finProdFinEquiv_apply_val]; ring
    have hlt : (a : ℕ) * m + j < (List.ofFn fun k ↦ (ts k : ℕ)).length := by
      rw [List.length_ofFn, hidx]
      exact (finProdFinEquiv (a, j)).2
    have hget : (List.ofFn fun k ↦ (ts k : ℕ)).getD (a * m + j) 0 =
        tN (e.symm j) (e.symm a) := by
      rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
      simp only [hts, hidx, Fin.eta, Equiv.symm_apply_apply]
    rw [hget, hC]
    push_cast
    rfl
  have hCclose : ∀ a, ∑ r, (C r a - V r a) ^ 2 ≤ ρ := by
    intro a
    have hpt : ∀ r, (C r a - V r a) ^ 2 ≤ (1 : ℝ) / ((S : ℝ) ^ 2 * G.1) := by
      intro r
      have h1 := htNclose r a
      rw [← sq_abs]
      have h2 : |C r a - V r a| ^ 2 ≤ (1 / (2 * (S * R))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      refine h2.trans ?_
      have hRsq : (G.1 : ℝ) / 4 ≤ (R : ℝ) ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hR1 2
        rw [div_pow, Real.sq_sqrt hnR.le] at this
        linarith
      rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul, mul_pow,
        mul_pow]
      nlinarith [sq_nonneg (S : ℝ)]
    calc ∑ r, (C r a - V r a) ^ 2 ≤ ∑ _r : ι, (1 : ℝ) / ((S : ℝ) ^ 2 * G.1) :=
          sum_le_sum fun r _ ↦ hpt r
      _ = (m : ℝ) / ((S : ℝ) ^ 2 * G.1) := by
          rw [sum_const, card_univ, hm, nsmul_eq_mul]; ring
      _ ≤ ρ := by
          rw [hρ, div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 := mul_le_mul_of_nonneg_right hS hnR.le
          have e1 : (m : ℝ) * (128 * m * G.1) = 128 * (m : ℝ) ^ 2 * G.1 := by ring
          have e2 : α ^ 2 * ((S : ℝ) ^ 2 * G.1) = α ^ 2 * (S : ℝ) ^ 2 * G.1 := by ring
          rw [e1, e2]
          exact h1
  -- the separation of the values
  have hsepV : ∀ a b, a ≠ b → 32 * ρ ≤ ∑ r, (V r a - V r b) ^ 2 := by
    intro a b hab
    obtain ⟨r, hr, hsepr⟩ := exists_sep χ hc hsize hn hα hsep hτ hab
    rw [hm] at hsepr
    refine le_trans ?_ (single_le_sum (fun r _ ↦ sq_nonneg (V r a - V r b)) (mem_univ r))
    have e1 : 32 * ρ = α ^ 2 / (4 * m * G.1) := by rw [hρ]; field_simp; ring
    rw [e1]
    simp only [hV, partValue, ite_eq_left hr]
    exact hsepr
  -- the tuple of net vectors
  refine ⟨fun j ↦ u (e.symm j), fun j ↦ hu _, ts, ?_⟩
  have hcount : (univ.filter fun y : Fin G.1 ↦ clusterIdxC (List.ofFn fun j ↦ u (e.symm j))
      (gridCenters m S K R (List.ofFn fun k ↦ (ts k : ℕ))) y ≠ e (χ y)) ⊆ B1 ∪ B2 := by
    intro y hy
    rw [mem_filter] at hy
    by_contra hyB
    rw [mem_union, not_or] at hyB
    exact hy.2 (clusterIdxC_good e _ _ (length_gridCenters _ _ _ _ _) Ur
      (fun r y ↦ by simp [hUr, Net.ratVec]) C V hCval hρpos hCclose hsepV (χ y) y
      (hgood y hyB.1 hyB.2))
  calc _ ≤ ((B1 ∪ B2).card : ℝ) := by exact_mod_cast card_le_card hcount
    _ ≤ (B1.card : ℝ) + B2.card := by exact_mod_cast card_union_le B1 B2
    _ ≤ F * G.1 + E * G.1 := add_le_add hB1c hB2c
    _ = (E + F) * G.1 := by ring

end Grid

end Alg

end BHSV25
