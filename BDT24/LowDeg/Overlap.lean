module

public import BDT24.LowDeg.Defs

/-!
# The overlap of two random spikes [BDT24, Lemma B.5]

`BDT24.LowDeg.overlapMoment_le`: for two independent uniform sign patterns,
`E ⟨x_u, x_v⟩^(2L) ≤ (C L)^L (1/d + L/k²)^L` for all `L ≥ 1`, with `C = 8e²`.

The overlap is `(1 + R)/(k + 1)` with `R = ∑ⱼ uⱼ vⱼ` (`OV.ovq_spikeIP_eq`); the first
coordinates contribute the `1`. The proof follows the paper's steps, bounding the moments of `R`
through its moment generating function:

* **Given the supports `S, S'`, `R` is a sum of `|S ∩ S'|` Rademacher signs**: the sign patterns
  are invariant under sign flips, and averaging over the flips gives
  `E e^{tR} = E ∏ⱼ cosh(t uⱼ vⱼ) = E cosh(t)^|S ∩ S'|` (`OV.ovq_avg`).
* **The overlap `|S ∩ S'|` is dominated by a binomial**: `P(T ⊆ S) ≤ (k/d)^|T|` (`OV.ovq_N_le`,
  by swapping coordinates and double counting), so expanding `∏ⱼ (1 + (cosh t - 1) 1[j ∈ S ∩ S'])`
  over subsets gives `E e^{tR} ≤ (1 + (cosh t - 1) (k/d)²)^d ≤ exp((cosh t - 1) k²/d)`
  (`OV.ovq_mgf_le_exp`).
* **Moments**: `(1 + R)^(2L) ≤ (2L)! t^(-2L) e (e^{tR} + e^{-tR})` for `0 < t ≤ 1`
  (`OV.ovq_pow_le`); with `t² = L/(k²/d + L)` and `cosh t - 1 ≤ t²`, and `(2L)! ≤ (2L)^(2L)`,
  this gives `E ⟨x_u, x_v⟩^(2L) ≤ 2e (4e L (1/d + L/k²))^L` (`OV.ovq_main`).
-/

@[expose] public section

namespace BDT24.LowDeg

namespace OV

open Finset Real

/-! ### The overlap in terms of the signs -/

/-- The correlation `∑ⱼ uⱼ vⱼ` of two sign patterns. -/
noncomputable def ovqCorr {d : ℕ} (u v : Fin d → SignType) : ℝ :=
  ∑ j, (u j : ℝ) * (v j : ℝ)

/-- The overlap of two spikes is `(1 + ∑ⱼ uⱼ vⱼ) / (k + 1)`. -/
theorem ovq_spikeIP_eq {d : ℕ} (k : ℕ) (u v : Fin d → SignType) :
    spikeIP k u v = (1 + ovqCorr u v) / ((k : ℝ) + 1) := by
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hs : √((k : ℝ) + 1) * √((k : ℝ) + 1) = (k : ℝ) + 1 := Real.mul_self_sqrt hpos.le
  have hne : √((k : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  unfold spikeIP spikeVector ovqCorr
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [add_div, Finset.sum_div]
  congr 1
  · rw [div_mul_div_comm, hs]
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_mul_div_comm, hs]

/-! ### Sign flips -/

/-- The sign flips: the patterns with all entries `±1`. -/
def ovqFlips (d : ℕ) : Finset (Fin d → SignType) :=
  Fintype.piFinset fun _ ↦ ({1, -1} : Finset SignType)

/-- A sign flip is an involution. -/
theorem ovq_flip_sq {e : SignType} (he : e ∈ ({1, -1} : Finset SignType)) (s : SignType) :
    e * (e * s) = s := by
  simp only [mem_insert, mem_singleton] at he
  rcases he with rfl | rfl <;> cases s <;> decide

/-- A sign flip keeps the support. -/
theorem ovq_flip_ne {e : SignType} (he : e ∈ ({1, -1} : Finset SignType)) (s : SignType) :
    e * s ≠ 0 ↔ s ≠ 0 := by
  simp only [mem_insert, mem_singleton] at he
  rcases he with rfl | rfl <;> cases s <;> decide

/-- Sign flips preserve the sign patterns with `k` nonzero entries. -/
theorem ovq_flip_mem {d k : ℕ} {ε v : Fin d → SignType} (hε : ε ∈ ovqFlips d)
    (hv : v ∈ spikeSigns d k) : ε * v ∈ spikeSigns d k := by
  rw [ovqFlips, Fintype.mem_piFinset] at hε
  unfold spikeSigns at hv ⊢
  rw [mem_filter] at hv ⊢
  refine ⟨mem_univ _, ?_⟩
  rw [← hv.2]
  congr 1
  exact filter_congr fun i _ => by simpa using ovq_flip_ne (hε i) (v i)

/-- Sums over the sign patterns are invariant under a sign flip. -/
theorem ovq_sum_flip {d k : ℕ} {ε : Fin d → SignType} (hε : ε ∈ ovqFlips d)
    (F : (Fin d → SignType) → ℝ) :
    ∑ v ∈ spikeSigns d k, F (ε * v) = ∑ v ∈ spikeSigns d k, F v := by
  have hinv : ∀ v : Fin d → SignType, ε * (ε * v) = v := fun v => by
    funext i
    rw [ovqFlips, Fintype.mem_piFinset] at hε
    simpa using ovq_flip_sq (hε i) (v i)
  exact Finset.sum_nbij' (fun v => ε * v) (fun v => ε * v) (fun v hv => ovq_flip_mem hε hv)
    (fun v hv => ovq_flip_mem hε hv) (fun v _ => hinv v) (fun v _ => hinv v) (fun v _ => rfl)

/-- There are `2^d` sign flips. -/
theorem ovq_card_flips (d : ℕ) : ((ovqFlips d).card : ℝ) = 2 ^ d := by
  have h2 : ({1, -1} : Finset SignType).card = 2 := by decide
  simp [ovqFlips, Fintype.card_piFinset, h2]

/-- **Averaging over sign flips**: the moment generating function of the correlation is an
average of products of hyperbolic cosines. -/
theorem ovq_avg {d k : ℕ} (u : Fin d → SignType) (t : ℝ) :
    ∑ v ∈ spikeSigns d k, exp (t * ovqCorr u v) =
      ∑ v ∈ spikeSigns d k, ∏ j, cosh (t * ((u j : ℝ) * (v j : ℝ))) := by
  have key : ∀ v : Fin d → SignType, ∑ ε ∈ ovqFlips d, exp (t * ovqCorr u (ε * v)) =
      2 ^ d * ∏ j, cosh (t * ((u j : ℝ) * (v j : ℝ))) := by
    intro v
    have h1 : ∀ ε : Fin d → SignType, exp (t * ovqCorr u (ε * v)) =
        ∏ j, exp (t * ((u j : ℝ) * ((ε j : ℝ) * (v j : ℝ)))) := by
      intro ε
      rw [ovqCorr, Finset.mul_sum, Real.exp_sum]
      simp [SignType.coe_mul]
    simp_rw [h1]
    rw [ovqFlips, ← Finset.prod_univ_sum (fun _ ↦ ({1, -1} : Finset SignType))
      (fun j e ↦ exp (t * ((u j : ℝ) * ((e : ℝ) * (v j : ℝ)))))]
    rw [show (2 : ℝ) ^ d = ∏ _j : Fin d, (2 : ℝ) by simp, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Finset.sum_pair (by decide : (1 : SignType) ≠ -1)]
    simp [Real.cosh_eq]
    ring
  have h2 : (2 : ℝ) ^ d * ∑ v ∈ spikeSigns d k, exp (t * ovqCorr u v) =
      (2 : ℝ) ^ d * ∑ v ∈ spikeSigns d k, ∏ j, cosh (t * ((u j : ℝ) * (v j : ℝ))) := by
    calc (2 : ℝ) ^ d * ∑ v ∈ spikeSigns d k, exp (t * ovqCorr u v)
        = ∑ ε ∈ ovqFlips d, ∑ v ∈ spikeSigns d k, exp (t * ovqCorr u (ε * v)) := by
          rw [Finset.sum_congr rfl fun ε hε =>
            ovq_sum_flip (k := k) hε (fun v => exp (t * ovqCorr u v)), Finset.sum_const,
            nsmul_eq_mul, ovq_card_flips]
      _ = ∑ v ∈ spikeSigns d k, ∑ ε ∈ ovqFlips d, exp (t * ovqCorr u (ε * v)) :=
          Finset.sum_comm
      _ = ∑ v ∈ spikeSigns d k, 2 ^ d * ∏ j, cosh (t * ((u j : ℝ) * (v j : ℝ))) :=
          Finset.sum_congr rfl fun v _ => key v
      _ = _ := (Finset.mul_sum _ _ _).symm
  exact mul_left_cancel₀ (by positivity) h2

/-! ### The probability that the support contains a given set -/

/-- The number of sign patterns with `k` nonzero entries whose support contains `T`. -/
def ovqN (d k : ℕ) (T : Finset (Fin d)) : ℕ :=
  ((spikeSigns d k).filter fun u ↦ ∀ j ∈ T, u j ≠ 0).card

/-- Permuting the coordinates preserves the sign patterns with `k` nonzero entries. -/
theorem ovq_comp_mem {d k : ℕ} (σ : Equiv.Perm (Fin d)) {u : Fin d → SignType}
    (hu : u ∈ spikeSigns d k) : u ∘ σ ∈ spikeSigns d k := by
  unfold spikeSigns at hu ⊢
  rw [mem_filter] at hu ⊢
  refine ⟨mem_univ _, ?_⟩
  rw [← hu.2]
  exact Finset.card_nbij' σ σ.symm (fun x hx => by simpa using hx)
    (fun x hx => by simpa using hx) (fun x _ => by simp) (fun x _ => by simp)

/-- Swapping two coordinates outside `T` moves the patterns whose support contains `T` and the
first coordinate to those whose support contains `T` and the second. -/
theorem ovq_swap_mem {d k : ℕ} {T : Finset (Fin d)} {i j : Fin d} (hi : i ∉ T) (hj : j ∉ T)
    {u : Fin d → SignType} (hu : u ∈ (spikeSigns d k).filter fun u ↦ ∀ x ∈ insert i T, u x ≠ 0) :
    u ∘ Equiv.swap i j ∈ (spikeSigns d k).filter fun u ↦ ∀ x ∈ insert j T, u x ≠ 0 := by
  rw [mem_filter] at hu ⊢
  refine ⟨ovq_comp_mem _ hu.1, ?_⟩
  intro x hx
  rw [mem_insert] at hx
  rcases hx with rfl | hx
  · simpa using hu.2 i (mem_insert_self _ _)
  · have : Equiv.swap i j x = x :=
      Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact hi hx) (by rintro rfl; exact hj hx)
    simpa [this] using hu.2 x (mem_insert_of_mem hx)

/-- The count `ovqN` does not depend on which coordinate outside `T` is added. -/
theorem ovq_N_swap {d k : ℕ} {T : Finset (Fin d)} {i j : Fin d} (hi : i ∉ T) (hj : j ∉ T) :
    ovqN d k (insert i T) = ovqN d k (insert j T) := by
  unfold ovqN
  have hinv : ∀ u : Fin d → SignType, (u ∘ Equiv.swap i j) ∘ Equiv.swap i j = u := fun u => by
    funext x
    simp
  refine Finset.card_nbij' (fun u => u ∘ Equiv.swap i j) (fun u => u ∘ Equiv.swap i j)
    (fun u hu => mem_coe.2 (ovq_swap_mem hi hj (mem_coe.1 hu))) (fun u hu => ?_)
    (fun u _ => hinv u) (fun u _ => hinv u)
  have := ovq_swap_mem hj hi (mem_coe.1 hu)
  rw [Equiv.swap_comm] at this
  exact mem_coe.2 this

/-- **Double counting**: summing over the coordinates outside `T` counts each pattern whose
support contains `T` once for each of its `k - |T|` other nonzero entries. -/
theorem ovq_sum_insert {d k : ℕ} (T : Finset (Fin d)) :
    ∑ j ∈ Tᶜ, ovqN d k (insert j T) = (k - T.card) * ovqN d k T := by
  unfold ovqN
  have h1 : ∀ j, ((spikeSigns d k).filter fun u ↦ ∀ x ∈ insert j T, u x ≠ 0) =
      ((spikeSigns d k).filter fun u ↦ ∀ x ∈ T, u x ≠ 0).filter fun u ↦ u j ≠ 0 := by
    intro j
    rw [filter_filter]
    exact filter_congr fun u _ => by rw [forall_mem_insert, and_comm]
  set ST := (spikeSigns d k).filter fun u ↦ ∀ x ∈ T, u x ≠ 0
  have h3 : ∀ u ∈ ST, (Tᶜ.filter fun x ↦ u x ≠ 0).card = k - T.card := by
    intro u hu
    rw [mem_filter] at hu
    have hT : T ⊆ univ.filter fun x ↦ u x ≠ 0 := fun x hx =>
      mem_filter.2 ⟨mem_univ _, hu.2 x hx⟩
    have hk : (univ.filter fun x ↦ u x ≠ 0).card = k := by
      have := hu.1
      unfold spikeSigns at this
      exact (mem_filter.1 this).2
    have h2 : Tᶜ.filter (fun x ↦ u x ≠ 0) = (univ.filter fun x ↦ u x ≠ 0) \ T := by
      ext x
      simp [and_comm]
    rw [h2, card_sdiff_of_subset hT, hk]
  calc ∑ j ∈ Tᶜ, ((spikeSigns d k).filter fun u ↦ ∀ x ∈ insert j T, u x ≠ 0).card
      = ∑ j ∈ Tᶜ, ∑ u ∈ ST, if u j ≠ 0 then 1 else 0 :=
        Finset.sum_congr rfl fun j _ => by rw [h1, card_filter]
    _ = ∑ u ∈ ST, ∑ j ∈ Tᶜ, if u j ≠ 0 then 1 else 0 := Finset.sum_comm
    _ = ∑ _u ∈ ST, (k - T.card) :=
        Finset.sum_congr rfl fun u hu => by rw [← card_filter, h3 u hu]
    _ = (k - T.card) * ST.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- **Adding one coordinate**: `d · N(T ∪ {i}) ≤ k · N(T)`, that is,
`P(T ∪ {i} ⊆ S) ≤ (k/d) P(T ⊆ S)`. -/
theorem ovq_N_step {d k : ℕ} {T : Finset (Fin d)} {i : Fin d} (hi : i ∉ T) :
    d * ovqN d k (insert i T) ≤ k * ovqN d k T := by
  have hsum : ∑ j ∈ Tᶜ, ovqN d k (insert j T) = (d - T.card) * ovqN d k (insert i T) := by
    rw [Finset.sum_congr rfl fun j hj => ovq_N_swap (mem_compl.1 hj) hi, sum_const, card_compl,
      Fintype.card_fin, smul_eq_mul]
  have hmono : ovqN d k (insert i T) ≤ ovqN d k T := by
    unfold ovqN
    refine card_le_card fun u hu => ?_
    rw [mem_filter] at hu ⊢
    exact ⟨hu.1, fun x hx => hu.2 x (mem_insert_of_mem hx)⟩
  have hTd : T.card ≤ d := by simpa using card_le_univ T
  by_cases hTk : T.card ≤ k
  · have h := ovq_sum_insert (k := k) T
    rw [hsum] at h
    calc d * ovqN d k (insert i T)
        = (d - T.card) * ovqN d k (insert i T) + T.card * ovqN d k (insert i T) := by
          rw [← add_mul, Nat.sub_add_cancel hTd]
      _ ≤ (k - T.card) * ovqN d k T + T.card * ovqN d k T := by
          rw [h]
          exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hmono) _
      _ = k * ovqN d k T := by rw [← add_mul, Nat.sub_add_cancel hTk]
  · have h0 : ovqN d k T = 0 := by
      unfold ovqN
      rw [card_eq_zero, filter_eq_empty_iff]
      intro u hu hall
      apply hTk
      unfold spikeSigns at hu
      rw [mem_filter] at hu
      rw [← hu.2]
      exact card_le_card fun x hx => mem_filter.2 ⟨mem_univ _, hall x hx⟩
    have : ovqN d k (insert i T) = 0 := Nat.eq_zero_of_le_zero (h0 ▸ hmono)
    simp [this, h0]

/-- **Containment**: `d^|T| N(T) ≤ k^|T| N`, that is, `P(T ⊆ S) ≤ (k/d)^|T|`. -/
theorem ovq_N_le {d k : ℕ} (T : Finset (Fin d)) :
    d ^ T.card * ovqN d k T ≤ k ^ T.card * (spikeSigns d k).card := by
  induction T using Finset.induction_on with
  | empty => simp [ovqN]
  | insert i T hi ih =>
    rw [card_insert_of_notMem hi, pow_succ, pow_succ]
    calc d ^ T.card * d * ovqN d k (insert i T) = d ^ T.card * (d * ovqN d k (insert i T)) := by
          ring
      _ ≤ d ^ T.card * (k * ovqN d k T) := Nat.mul_le_mul_left _ (ovq_N_step hi)
      _ = k * (d ^ T.card * ovqN d k T) := by ring
      _ ≤ k * (k ^ T.card * (spikeSigns d k).card) := Nat.mul_le_mul_left _ ih
      _ = k ^ T.card * k * (spikeSigns d k).card := by ring

/-- `N(T) ≤ (k/d)^|T| N` in the reals. -/
theorem ovq_N_le_real {d k : ℕ} (hd : 0 < d) (T : Finset (Fin d)) :
    (ovqN d k T : ℝ) ≤ ((k : ℝ) / d) ^ T.card * (spikeSigns d k).card := by
  have h' : (d : ℝ) ^ T.card * ovqN d k T ≤ (k : ℝ) ^ T.card * (spikeSigns d k).card := by
    exact_mod_cast ovq_N_le T
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-! ### The moment generating function of the correlation -/

/-- The indicator that a sign is nonzero. -/
noncomputable def ovqB (s : SignType) : ℝ := if s ≠ 0 then 1 else 0

/-- `cosh (x sₜ) = 1 + (cosh x - 1) 1[s ≠ 0] 1[t ≠ 0]` for signs `s, t`. -/
theorem ovq_cosh (x : ℝ) (s t : SignType) :
    cosh (x * ((s : ℝ) * (t : ℝ))) = 1 + (cosh x - 1) * (ovqB s * ovqB t) := by
  cases s <;> cases t <;> simp [ovqB]

/-- Summing the indicator of `T ⊆ supp u` counts `ovqN`. -/
theorem ovq_sum_prodB {d k : ℕ} (T : Finset (Fin d)) :
    ∑ u ∈ spikeSigns d k, ∏ j ∈ T, ovqB (u j) = ovqN d k T := by
  unfold ovqB ovqN
  simp_rw [Finset.prod_boole]
  rw [Finset.natCast_card_filter]
  exact Finset.sum_congr rfl fun _ _ => by congr

/-- `1 ≤ cosh x`. -/
theorem ovq_one_le_cosh (x : ℝ) : 1 ≤ cosh x := by
  nlinarith [Real.cosh_sq x, Real.cosh_pos x, sq_nonneg (Real.sinh x)]

/-- **The moment generating function of the correlation**:
`∑_{u,v} e^{t ⟨u, v⟩} ≤ N² (1 + (cosh t - 1) (k/d)²)^d`. -/
theorem ovq_mgf_le {d k : ℕ} (hd : 0 < d) (t : ℝ) :
    ∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k, exp (t * ovqCorr u v) ≤
      ((spikeSigns d k).card : ℝ) ^ 2 * (1 + (cosh t - 1) * ((k : ℝ) / d) ^ 2) ^ d := by
  set y := cosh t - 1 with hy_def
  have hy : 0 ≤ y := by linarith [ovq_one_le_cosh t]
  set N : ℝ := ((spikeSigns d k).card : ℝ)
  have hexp : ∀ u v : Fin d → SignType, ∏ j, cosh (t * ((u j : ℝ) * (v j : ℝ))) =
      ∑ T ∈ (univ : Finset (Fin d)).powerset,
        y ^ T.card * ((∏ j ∈ T, ovqB (u j)) * ∏ j ∈ T, ovqB (v j)) := by
    intro u v
    simp_rw [ovq_cosh, Finset.prod_one_add]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [prod_mul_distrib, prod_mul_distrib, prod_const]
  calc ∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k, exp (t * ovqCorr u v)
      = ∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k,
          ∑ T ∈ (univ : Finset (Fin d)).powerset,
            y ^ T.card * ((∏ j ∈ T, ovqB (u j)) * ∏ j ∈ T, ovqB (v j)) :=
        Finset.sum_congr rfl fun u _ => by
          rw [ovq_avg]
          exact Finset.sum_congr rfl fun v _ => hexp u v
    _ = ∑ T ∈ (univ : Finset (Fin d)).powerset, y ^ T.card * ((ovqN d k T : ℝ) * ovqN d k T) := by
        rw [Finset.sum_congr rfl fun u _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [← ovq_sum_prodB, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ T ∈ (univ : Finset (Fin d)).powerset,
          y ^ T.card * ((((k : ℝ) / d) ^ T.card * N) * (((k : ℝ) / d) ^ T.card * N)) := by
        refine Finset.sum_le_sum fun T _ => ?_
        have h1 := ovq_N_le_real (k := k) hd T
        have h0 : (0 : ℝ) ≤ ovqN d k T := Nat.cast_nonneg _
        gcongr
    _ = N ^ 2 * ∑ T ∈ (univ : Finset (Fin d)).powerset, ∏ _j ∈ T, (y * ((k : ℝ) / d) ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [prod_const]
        ring_nf
    _ = N ^ 2 * (1 + y * ((k : ℝ) / d) ^ 2) ^ d := by
        rw [← Finset.prod_one_add, prod_const, card_univ, Fintype.card_fin]

/-- The moment generating function in exponential form:
`∑_{u,v} e^{t ⟨u, v⟩} ≤ N² exp((cosh t - 1) k²/d)`. -/
theorem ovq_mgf_le_exp {d k : ℕ} (hd : 0 < d) (t : ℝ) :
    ∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k, exp (t * ovqCorr u v) ≤
      ((spikeSigns d k).card : ℝ) ^ 2 * exp ((cosh t - 1) * ((k : ℝ) ^ 2 / d)) := by
  refine (ovq_mgf_le hd t).trans ?_
  have hy : 0 ≤ cosh t - 1 := by linarith [ovq_one_le_cosh t]
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  gcongr
  calc (1 + (cosh t - 1) * ((k : ℝ) / d) ^ 2) ^ d
      ≤ exp ((cosh t - 1) * ((k : ℝ) / d) ^ 2) ^ d := by
        gcongr
        linarith [Real.add_one_le_exp ((cosh t - 1) * ((k : ℝ) / d) ^ 2)]
    _ = exp ((cosh t - 1) * ((k : ℝ) ^ 2 / d)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp

/-! ### From the moment generating function to the moments -/

/-- `(1 + y)^(2L) ≤ (2L)!/t^(2L) · e · (e^{ty} + e^{-ty})` for `0 < t ≤ 1`. -/
theorem ovq_pow_le (L : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (y : ℝ) :
    (1 + y) ^ (2 * L) ≤
      (2 * L).factorial / t ^ (2 * L) * (exp 1 * (exp (t * y) + exp (-t * y))) := by
  have hf : (0 : ℝ) < (2 * L).factorial := by positivity
  have h1 : (t * |1 + y|) ^ (2 * L) / (2 * L).factorial ≤ exp (t * |1 + y|) :=
    Real.pow_div_factorial_le_exp _ (by positivity) _
  have h2 : exp (t * |1 + y|) ≤ exp 1 * (exp (t * y) + exp (-t * y)) := by
    have e1 : exp t ≤ exp 1 := exp_le_exp.2 ht1
    have e2 : exp (-t) ≤ exp 1 := exp_le_exp.2 (by linarith)
    have p1 := exp_pos (t * y)
    have p2 := exp_pos (-t * y)
    have p0 := exp_pos 1
    rcases abs_cases (1 + y) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h, mul_add, mul_one, exp_add]
      have := mul_le_mul_of_nonneg_right e1 p1.le
      have := mul_pos p0 p2
      linarith
    · rw [h, show t * -(1 + y) = -t + -t * y by ring, exp_add]
      have := mul_le_mul_of_nonneg_right e2 p2.le
      have := mul_pos p0 p1
      linarith
  have h3 : (t * |1 + y|) ^ (2 * L) = t ^ (2 * L) * (1 + y) ^ (2 * L) := by
    rw [mul_pow, (even_two_mul L).pow_abs]
  rw [h3, div_le_iff₀ hf] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h4 := mul_le_mul_of_nonneg_left h2 hf.le
  linarith

/-- `cosh t - 1 ≤ t²` for `t² ≤ 1`. -/
theorem ovq_cosh_sub_one_le {t : ℝ} (ht : t ^ 2 ≤ 1) : cosh t - 1 ≤ t ^ 2 := by
  have h1 : |t| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    exact ht
  have h2 : |-t| ≤ 1 := by rwa [abs_neg]
  have h3 := Real.abs_exp_sub_one_sub_id_le h1
  have h4 := Real.abs_exp_sub_one_sub_id_le h2
  have h5 := le_abs_self (exp t - 1 - t)
  have h6 := le_abs_self (exp (-t) - 1 - -t)
  rw [Real.cosh_eq]
  rw [neg_sq] at h4
  linarith

/-- `(2L)! / (t^(2L) (k+1)^(2L)) ≤ (4 L B)^L` when `t² k² = L / B`. -/
theorem ovq_fact_le {k L : ℕ} {t B : ℝ} (ht : 0 < t) (hB : 0 < B) (hk : (1 : ℝ) ≤ k)
    (hL : (1 : ℝ) ≤ L) (htk : t ^ 2 * (k : ℝ) ^ 2 = L / B) :
    (2 * L).factorial / t ^ (2 * L) / ((k : ℝ) + 1) ^ (2 * L) ≤ (4 * L * B) ^ L := by
  have hfac : ((2 * L).factorial : ℝ) ≤ (4 * (L : ℝ) ^ 2) ^ L := by
    have h : ((2 * L).factorial : ℝ) ≤ ((2 * L : ℕ) : ℝ) ^ (2 * L) := by
      exact_mod_cast Nat.factorial_le_pow (2 * L)
    refine h.trans (le_of_eq ?_)
    push_cast
    rw [pow_mul]
    ring
  have hden : (t ^ 2 * (k : ℝ) ^ 2) ^ L ≤ t ^ (2 * L) * ((k : ℝ) + 1) ^ (2 * L) := by
    rw [pow_mul, pow_mul, mul_pow]
    gcongr
    linarith
  have hpos : 0 < (t ^ 2 * (k : ℝ) ^ 2) ^ L := by positivity
  calc (2 * L).factorial / t ^ (2 * L) / ((k : ℝ) + 1) ^ (2 * L)
      = (2 * L).factorial / (t ^ (2 * L) * ((k : ℝ) + 1) ^ (2 * L)) := by rw [div_div]
    _ ≤ (4 * (L : ℝ) ^ 2) ^ L / (t ^ 2 * (k : ℝ) ^ 2) ^ L :=
        div_le_div₀ (by positivity) hfac hpos hden
    _ = (4 * L * B) ^ L := by
        rw [← div_pow, htk]
        congr 1
        field_simp

/-- **The overlap moment bound** with the explicit constant `8 e²`. -/
theorem ovq_main {d k L : ℕ} (hk : 1 ≤ k) (hkd : k ≤ d) (hL : 1 ≤ L) :
    overlapMoment d k L ≤ (8 * exp 1 ^ 2 * L) ^ L * (1 / d + L / k ^ 2) ^ L := by
  have hd : 0 < d := by omega
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set B : ℝ := 1 / d + L / k ^ 2 with hB
  have hBpos : 0 < B := by positivity
  set A : ℝ := (k : ℝ) ^ 2 / d + L with hA
  have hApos : 0 < A := by positivity
  have hAB : A = (k : ℝ) ^ 2 * B := by
    rw [hA, hB]
    field_simp
  set t : ℝ := √(L / A) with ht
  have htpos : 0 < t := Real.sqrt_pos.2 (by positivity)
  have ht2 : t ^ 2 = L / A := Real.sq_sqrt (by positivity)
  have hLA : (L : ℝ) / A ≤ 1 := by
    rw [div_le_one hApos, hA]
    linarith [show 0 ≤ (k : ℝ) ^ 2 / d by positivity]
  have ht1 : t ≤ 1 := Real.sqrt_le_one.2 hLA
  have htk : t ^ 2 * (k : ℝ) ^ 2 = L / B := by
    rw [ht2, hAB]
    field_simp
  have hexpo : (cosh t - 1) * ((k : ℝ) ^ 2 / d) ≤ L := by
    have h1 := ovq_cosh_sub_one_le (ht2 ▸ hLA)
    have h2 : 0 ≤ (k : ℝ) ^ 2 / d := by positivity
    calc (cosh t - 1) * ((k : ℝ) ^ 2 / d) ≤ t ^ 2 * ((k : ℝ) ^ 2 / d) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = L * ((k : ℝ) ^ 2 / d / A) := by rw [ht2]; ring
      _ ≤ L * 1 := by
          gcongr
          rw [div_le_one hApos, hA]
          linarith
      _ = L := mul_one _
  set N : ℝ := ((spikeSigns d k).card : ℝ) with hN
  have hM : ∀ s : ℝ, cosh s = cosh t →
      ∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k, exp (s * ovqCorr u v) ≤ N ^ 2 * exp L := by
    intro s hs
    refine (ovq_mgf_le_exp hd s).trans ?_
    rw [hs]
    gcongr
  have hRHS : 0 ≤ (8 * exp 1 ^ 2 * L) ^ L * B ^ L := by positivity
  rcases (Nat.cast_nonneg _ : (0 : ℝ) ≤ N).eq_or_lt with h0 | hNpos
  · rw [overlapMoment, ← h0]
    simpa using hRHS
  set F : ℝ := (2 * L).factorial / t ^ (2 * L) with hF
  have hFpos : 0 < F := by positivity
  have hsum : ∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k, spikeIP k u v ^ (2 * L) ≤
      F / ((k : ℝ) + 1) ^ (2 * L) * exp 1 * (2 * (N ^ 2 * exp L)) := by
    calc ∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k, spikeIP k u v ^ (2 * L)
        = ∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k,
            (1 + ovqCorr u v) ^ (2 * L) / ((k : ℝ) + 1) ^ (2 * L) := by
          simp_rw [ovq_spikeIP_eq, div_pow]
      _ ≤ ∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k,
            F * (exp 1 * (exp (t * ovqCorr u v) + exp (-t * ovqCorr u v))) /
              ((k : ℝ) + 1) ^ (2 * L) := by
          gcongr with u _ v _
          exact ovq_pow_le L htpos ht1 _
      _ = F / ((k : ℝ) + 1) ^ (2 * L) * exp 1 *
            (∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k, exp (t * ovqCorr u v) +
              ∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k, exp (-t * ovqCorr u v)) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          ring
      _ ≤ F / ((k : ℝ) + 1) ^ (2 * L) * exp 1 * (N ^ 2 * exp L + N ^ 2 * exp L) := by
          gcongr
          · exact hM t rfl
          · exact hM (-t) (Real.cosh_neg t)
      _ = _ := by ring
  have hFK : F / ((k : ℝ) + 1) ^ (2 * L) ≤ (4 * L * B) ^ L := ovq_fact_le htpos hBpos hkr hLr htk
  have h2e : 2 * exp 1 ≤ (2 * exp 1) ^ L :=
    le_self_pow₀ (by linarith [Real.add_one_le_exp 1]) (by omega)
  calc overlapMoment d k L
      = (∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k, spikeIP k u v ^ (2 * L)) / N ^ 2 := rfl
    _ ≤ F / ((k : ℝ) + 1) ^ (2 * L) * exp 1 * (2 * (N ^ 2 * exp L)) / N ^ 2 := by gcongr
    _ = F / ((k : ℝ) + 1) ^ (2 * L) * (2 * exp 1) * exp 1 ^ L := by
        have hNne : N ≠ 0 := hNpos.ne'
        rw [Real.exp_one_pow]
        field_simp
    _ ≤ (4 * L * B) ^ L * (2 * exp 1) ^ L * exp 1 ^ L := by gcongr
    _ = (8 * exp 1 ^ 2 * L) ^ L * B ^ L := by
        rw [← mul_pow, ← mul_pow, ← mul_pow]
        congr 1
        ring

end OV

/-- **The moments of the overlap of two random spikes.** -/
theorem overlapMoment_le : ∃ C : ℝ, 0 < C ∧ ∀ d k L : ℕ, 1 ≤ k → k ≤ d → 1 ≤ L →
    overlapMoment d k L ≤ (C * L) ^ L * (1 / d + L / k ^ 2) ^ L :=
  ⟨8 * Real.exp 1 ^ 2, by positivity, fun _ _ _ hk hkd hL ↦ OV.ovq_main hk hkd hL⟩

end BDT24.LowDeg
