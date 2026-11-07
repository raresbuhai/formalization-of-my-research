module

public import BGHKLMM26.IntGap.Instance
public import Complexity.Foundations.BooleanAnalysis.Hypercontractivity
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Soundness of the integrality gap instance

`BGHKLMM26.IntGap.kvInst_value_le`: every labeling of `kvInst k z` satisfies at most a
`2^{-k η / 8}` fraction of the constraints, `η = z/2^k ≤ 1/4`.

Proof (the label-extended graph and hypercontractivity, as in [KV15, Lemma 3.3]): a labeling of
the right vertices picks one function in each class, a set `A ⊆ Fn k` of measure `μ ≤ 1/N`,
`N = 2^k` (`BGHKLMM26.IntGap.Snd.chosen`). A left vertex `(Q, Z)` with label `s` satisfies its
constraint to `[rep Q + e]` only if `rep Q + χ_s + e ∈ A`
(`BGHKLMM26.IntGap.Snd.mem_chosen_of_sat`), so it satisfies at most `c_Z(rep Q + χ_s)` of its
constraints, where `c_Z(g) = #{e vanishing outside Z : g + e ∈ A}`. By Cauchy–Schwarz, and since
the functions `rep Q + χ_s` of the left vertices `(Q, Z)` are distinct for each `Z`,
`(Σ_{(Q, Z)} c_Z)² ≤ |Lft| Σ_Z Σ_g c_Z(g)²`. On the cube `{0,1}^{Pt k}`
(`BGHKLMM26.IntGap.Snd.cubeEquiv`), `Σ_g c_Z(g)² = 2^{2^k} 4^z Σ_{S ∩ Z = ∅} 1̂_A(S)²`
(`BGHKLMM26.IntGap.Snd.sum_sq_count`), and a uniform `z`-set `Z` avoids `S` with probability
`C(N - |S|, z) / C(N, z) ≤ ρ^{|S|}`, `ρ = 1 - η`. So the second moment is at most
`Stab_ρ(1_A) ≤ ‖1_A‖²_{1+ρ} = μ^{2/(1+ρ)}` (complexitylib's `noiseStability_le_lpNorm_sq`), and
`value² ≤ μ^{2/(1+ρ) - 1} = μ^{η/(2-η)} ≤ N^{-η/4}`, so `value ≤ N^{-η/8}`. The hypothesis
`1 ≤ k` is not needed.
-/

@[expose] public section

namespace BGHKLMM26.IntGap.Snd

open UniqueGames

open Finset
open scoped BigOperators

variable {k z : ℕ}

/-- A bit of `ZMod 2` as a Boolean. -/
def bitEquiv : ZMod 2 ≃ Bool where
  toFun a := decide (a = 1)
  invFun b := if b then 1 else 0
  left_inv := by decide
  right_inv := by decide

/-- `bitEquiv` turns addition into exclusive or. -/
theorem bitEquiv_add (a b : ZMod 2) : bitEquiv (a + b) = bitEquiv a + bitEquiv b := by
  revert a b; decide

/-- Boolean functions on `Pt k` as points of the cube `Pt k → Bool`. -/
def cubeEquiv (k : ℕ) : Fn k ≃ (Pt k → Bool) := Equiv.piCongrRight fun _ ↦ bitEquiv

/-- `cubeEquiv` acts pointwise. -/
theorem cubeEquiv_apply (g : Fn k) (x : Pt k) : cubeEquiv k g x = bitEquiv (g x) := rfl

/-- `cubeEquiv` turns addition into exclusive or. -/
theorem cubeEquiv_add (f g : Fn k) : cubeEquiv k (f + g) = cubeEquiv k f + cubeEquiv k g :=
  funext fun x ↦ bitEquiv_add (f x) (g x)

open Cslib.BitString in
/-- **Parseval for a sum of translates**: the Fourier coefficient of `y ↦ Σ_e F (y + a e)` at `S`
is `F̂(S) Σ_e χ_S(a e)`. -/
theorem expect_sq_sum_translate {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → Bool) → ℝ) (s : Finset α) (a : α → ι → Bool) :
    𝔼 y, (∑ e ∈ s, F (y + a e)) ^ 2 =
      ∑ S, (fourierCoeff F S * ∑ e ∈ s, Cslib.BitString.chi ℝ S (a e)) ^ 2 := by
  have h : (fun y ↦ ∑ e ∈ s, F (y + a e)) = fun y ↦
      ∑ S, (fourierCoeff F S * ∑ e ∈ s, Cslib.BitString.chi ℝ S (a e)) *
        Cslib.BitString.chi ℝ S y := by
    funext y
    calc ∑ e ∈ s, F (y + a e)
        = ∑ e ∈ s, ∑ S, fourierCoeff F S * Cslib.BitString.chi ℝ S (y + a e) :=
          sum_congr rfl fun e _ ↦ (sum_fourierCoeff_mul_chi F _).symm
      _ = _ := by
          rw [sum_comm]
          refine sum_congr rfl fun S _ ↦ ?_
          rw [mul_sum, sum_mul]
          refine sum_congr rfl fun e _ ↦ ?_
          rw [Cslib.BitString.chi_add]
          ring
  rw [expect_sq_eq_sum_fourierCoeff_sq, h]
  exact sum_congr rfl fun S _ ↦ by rw [fourierCoeff_sum_mul_chi]

/-- The functions vanishing outside `Z` are the functions on `Z`. -/
def suppEquiv (Z : Finset (Pt k)) : {e : Fn k // Supp Z e} ≃ (Z → ZMod 2) where
  toFun e i := e.1 i
  invFun f := ⟨fun x ↦ if h : x ∈ Z then f ⟨x, h⟩ else 0, fun x hx ↦ by simp [hx]⟩
  left_inv e := by
    refine Subtype.ext (funext fun x ↦ ?_)
    by_cases h : x ∈ Z
    · simp [h]
    · simp [h, e.2 x h]
  right_inv f := funext fun i ↦ by simp

open Classical in
/-- There are `2^|Z|` functions vanishing outside `Z`. -/
theorem card_suppFn (Z : Finset (Pt k)) : #{e : Fn k | Supp Z e} = 2 ^ #Z := by
  rw [← Fintype.card_subtype, Fintype.card_congr (suppEquiv Z)]
  simp [ZMod.card]

/-- The character of `S` is `-1` at a point mass at a point of `S`. -/
theorem chi_cube_single {S : Finset (Pt k)} {x : Pt k} (hx : x ∈ S) :
    Cslib.BitString.chi ℝ S (cubeEquiv k (Pi.single x 1)) = -1 := by
  unfold Cslib.BitString.chi
  rw [prod_eq_single_of_mem x hx]
  · simp [cubeEquiv_apply, bitEquiv]
  · intro i _ hi
    simp [cubeEquiv_apply, bitEquiv, Pi.single_eq_of_ne hi]

open Classical in
/-- **The character sums over the noise**: `Σ_{e vanishing outside Z} χ_S(e)` is the number of
such `e` if `S` and `Z` are disjoint and `0` otherwise. -/
theorem sum_supp_chi (Z S : Finset (Pt k)) :
    ∑ e with Supp Z e, Cslib.BitString.chi ℝ S (cubeEquiv k e) =
      if Disjoint S Z then (#{e : Fn k | Supp Z e} : ℝ) else 0 := by
  split_ifs with h
  · rw [natCast_card_filter, sum_filter]
    refine sum_congr rfl fun e _ ↦ ?_
    split_ifs with he
    · unfold Cslib.BitString.chi
      refine prod_eq_one fun i hi ↦ ?_
      simp [cubeEquiv_apply, bitEquiv, he i (disjoint_left.1 h hi)]
    · rfl
  · obtain ⟨x, hxS, hxZ⟩ := not_disjoint_iff.1 h
    have hsupp (e : Fn k) : Supp Z (e + Pi.single x 1) ↔ Supp Z e := by
      refine forall_congr' fun y ↦ imp_congr_right fun hy ↦ ?_
      have hyx : y ≠ x := fun h ↦ hy (h ▸ hxZ)
      simp [Pi.single_eq_of_ne hyx]
    rw [sum_filter]
    have hT : (∑ e, if Supp Z e then Cslib.BitString.chi ℝ S (cubeEquiv k e) else 0) =
        -∑ e, if Supp Z e then Cslib.BitString.chi ℝ S (cubeEquiv k e) else 0 := by
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addRight (Pi.single x 1 : Fn k))]
      simp only [Equiv.coe_addRight, hsupp, cubeEquiv_add, Cslib.BitString.chi_add,
        chi_cube_single hxS, ← sum_neg_distrib]
      refine sum_congr rfl fun e _ ↦ ?_
      split_ifs <;> ring
    linarith

/-- `C(N - s, z) ≤ C(N, z) (1 - z/N)^s`: a uniform `z`-set of `N` points avoids `s` given points
with probability at most `(1 - z/N)^s`. -/
theorem choose_sub_le {N z : ℕ} (hz : z ≤ N) (hN : 0 < N) :
    ∀ s ≤ N, ((N - s).choose z : ℝ) ≤ N.choose z * (1 - z / N) ^ s := by
  intro s
  induction s with
  | zero => intro _; simp
  | succ s ih =>
    intro hs
    obtain ⟨m, hm1, hm2⟩ : ∃ m, N - (s + 1) = m ∧ N - s = m + 1 := ⟨_, rfl, by omega⟩
    have hmN : m + 1 ≤ N := by omega
    have hih := ih (by omega)
    rw [hm2] at hih
    rw [hm1]
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hmN' : (m : ℝ) + 1 ≤ N := by exact_mod_cast hmN
    have hr : 0 ≤ 1 - (z : ℝ) / N := by
      rw [sub_nonneg, div_le_one hNr]; exact_mod_cast hz
    have key : (m.choose z : ℝ) * (m + 1) = ((m + 1).choose z : ℝ) * ((m + 1 - z : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_mul_succ_eq m z
    have hsub : ((m + 1 - z : ℕ) : ℝ) ≤ (m + 1) * (1 - z / N) := by
      rcases le_or_gt z (m + 1) with h | h
      · rw [Nat.cast_sub h]
        push_cast
        have : ((m : ℝ) + 1) * z / N ≤ z := by
          rw [div_le_iff₀ hNr]; nlinarith [(Nat.cast_nonneg z : (0 : ℝ) ≤ z)]
        rw [mul_sub, mul_one, mul_div_assoc']
        linarith
      · rw [Nat.sub_eq_zero_of_le h.le]; push_cast; positivity
    have hC : (0 : ℝ) ≤ ((m + 1).choose z : ℝ) := Nat.cast_nonneg _
    have h1 : (m.choose z : ℝ) ≤ ((m + 1).choose z : ℝ) * (1 - z / N) := by
      refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < m + 1)
      rw [key]
      calc ((m + 1).choose z : ℝ) * ((m + 1 - z : ℕ) : ℝ)
          ≤ ((m + 1).choose z : ℝ) * ((m + 1) * (1 - z / N)) :=
            mul_le_mul_of_nonneg_left hsub hC
        _ = _ := by ring
    calc (m.choose z : ℝ) ≤ ((m + 1).choose z : ℝ) * (1 - z / N) := h1
      _ ≤ N.choose z * (1 - z / N) ^ s * (1 - z / N) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hih) hr
      _ = _ := by ring

/-- A uniform `z`-set of points avoids a set `S` with probability at most `(1 - z/2^k)^{|S|}`. -/
theorem sum_disjoint_le (hz : z ≤ 2 ^ k) (S : Finset (Pt k)) :
    ∑ Z : {Z : Finset (Pt k) // #Z = z}, (if Disjoint S Z.1 then (1 : ℝ) else 0) ≤
      ((2 ^ k).choose z : ℝ) * (1 - z / 2 ^ k) ^ #S := by
  rw [← sum_subtype (powersetCard z univ) (fun Z ↦ by simp [mem_powersetCard])
    (fun Z ↦ if Disjoint S Z then (1 : ℝ) else 0), sum_boole]
  have h : (powersetCard z univ).filter (fun Z ↦ Disjoint S Z) = powersetCard z Sᶜ := by
    ext Z; simp [mem_powersetCard, subset_compl_iff_disjoint_left, and_comm]
  have hN : Fintype.card (Pt k) = 2 ^ k := card_lab k
  rw [h, card_powersetCard, card_compl, hN]
  have := choose_sub_le hz (by positivity) #S (hN ▸ card_le_univ S)
  push_cast at this
  exact this

/-- The indicator of a set of Boolean functions. -/
noncomputable def ind (A : Finset (Fn k)) (g : Fn k) : ℝ := if g ∈ A then 1 else 0

/-- The indicator of a set of Boolean functions, on the cube. -/
noncomputable def cubeInd (A : Finset (Fn k)) (y : Pt k → Bool) : ℝ := ind A ((cubeEquiv k).symm y)

/-- The cube has as many points as there are Boolean functions. -/
theorem card_cube : Fintype.card (Pt k → Bool) = Fintype.card (Fn k) :=
  (Fintype.card_congr (cubeEquiv k)).symm

open Classical Cslib.BitString in
/-- The second moment of the number of `e` vanishing outside `Z` with `g + e ∈ A`, in Fourier:
`Σ_g (Σ_e 1_A(g + e))² = 2^{2^k} 4^{|Z|} Σ_{S ∩ Z = ∅} 1̂_A(S)²`. -/
theorem sum_sq_count (A : Finset (Fn k)) (Z : Finset (Pt k)) :
    ∑ g : Fn k, (∑ e with Supp Z e, ind A (g + e)) ^ 2 =
      Fintype.card (Fn k) * (2 ^ #Z) ^ 2 *
        ∑ S, fourierCoeff (cubeInd A) S ^ 2 * (if Disjoint S Z then 1 else 0) := by
  have h1 (g : Fn k) : ∑ e with Supp Z e, ind A (g + e) =
      ∑ e with Supp Z e, cubeInd A (cubeEquiv k g + cubeEquiv k e) := by
    simp [cubeInd, ← cubeEquiv_add]
  simp_rw [h1]
  rw [Equiv.sum_comp (cubeEquiv k)
    fun y : Pt k → Bool ↦ (∑ e with Supp Z e, cubeInd A (y + cubeEquiv k e)) ^ 2]
  have h2 := Fintype.expect_eq_sum_div_card
    (fun y : Pt k → Bool ↦ (∑ e with Supp Z e, cubeInd A (y + cubeEquiv k e)) ^ 2)
  rw [expect_sq_sum_translate, card_cube] at h2
  have hM : (0 : ℝ) < Fintype.card (Fn k) := by exact_mod_cast Fintype.card_pos
  rw [eq_div_iff hM.ne'] at h2
  rw [← h2, sum_mul, mul_sum]
  refine sum_congr rfl fun S _ ↦ ?_
  rw [sum_supp_chi, card_suppFn]
  split_ifs <;> push_cast <;> ring

open Classical Cslib.BitString in
/-- **The noise bound**: summed over the `z`-sets `Z`, the second moments are at most
`2^{2^k} 4^z C(2^k, z) Stab_ρ(1_A)` with `ρ = 1 - z/2^k`. -/
theorem sum_sum_sq_le (A : Finset (Fn k)) (hz : z ≤ 2 ^ k) :
    ∑ Z : {Z : Finset (Pt k) // #Z = z}, ∑ g : Fn k, (∑ e with Supp Z.1 e, ind A (g + e)) ^ 2 ≤
      Fintype.card (Fn k) * (2 ^ z) ^ 2 * ((2 ^ k).choose z : ℝ) *
        noiseStability (1 - z / 2 ^ k) (cubeInd A) := by
  have h (Z : {Z : Finset (Pt k) // #Z = z}) :
      ∑ g : Fn k, (∑ e with Supp Z.1 e, ind A (g + e)) ^ 2 = Fintype.card (Fn k) * (2 ^ z) ^ 2 *
        ∑ S, fourierCoeff (cubeInd A) S ^ 2 * (if Disjoint S Z.1 then 1 else 0) := by
    rw [sum_sq_count, Z.2]
  simp_rw [h]
  calc ∑ Z : {Z : Finset (Pt k) // #Z = z}, (Fintype.card (Fn k) : ℝ) * (2 ^ z) ^ 2 *
        ∑ S, fourierCoeff (cubeInd A) S ^ 2 * (if Disjoint S Z.1 then 1 else 0)
      = Fintype.card (Fn k) * (2 ^ z) ^ 2 * ∑ S, fourierCoeff (cubeInd A) S ^ 2 *
          ∑ Z : {Z : Finset (Pt k) // #Z = z}, (if Disjoint S Z.1 then (1 : ℝ) else 0) := by
        rw [← mul_sum, sum_comm]
        simp_rw [mul_sum]
    _ ≤ Fintype.card (Fn k) * (2 ^ z) ^ 2 * ∑ S, fourierCoeff (cubeInd A) S ^ 2 *
          (((2 ^ k).choose z : ℝ) * (1 - z / 2 ^ k) ^ #S) := by
        gcongr with S
        exact sum_disjoint_le hz S
    _ = _ := by
        rw [noiseStability_eq_sum, mul_sum, mul_sum]
        exact sum_congr rfl fun S _ ↦ by ring

open Cslib Cslib.BitString in
/-- **Hypercontractivity** for an indicator: `Stab_ρ(1_A) ≤ ‖1_A‖²_{1+ρ} = μ^{2/(1+ρ)}`, where
`μ = |A| / 2^{2^k}` is the measure of `A`. -/
theorem stab_le (A : Finset (Fn k)) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) :
    noiseStability ρ (cubeInd A) ≤ (#A / Fintype.card (Fn k) : ℝ) ^ ((1 + ρ)⁻¹ * 2) := by
  have h := noiseStability_le_lpNorm_sq hρ hρ' (cubeInd A)
  have habs (y : Pt k → Bool) : |cubeInd A y| ^ (1 + ρ) = cubeInd A y := by
    unfold cubeInd ind
    split_ifs
    · simp
    · simp [Real.zero_rpow (by linarith : 1 + ρ ≠ 0)]
  have hE : 𝔼 y, cubeInd A y = #A / Fintype.card (Fn k) := by
    rw [Fintype.expect_eq_sum_div_card, card_cube, ← Equiv.sum_comp (cubeEquiv k)]
    simp [cubeInd, ind]
  rw [lpNorm] at h
  simp_rw [habs, hE] at h
  rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at h

/-- `rep P + χ_s` lies in the class `P`. -/
theorem mk_rep_add_chi (P : Cls k) (s : Lab k) : ((rep P + chi s : Fn k) : Cls k) = P := by
  rw [QuotientAddGroup.mk_add,
    (QuotientAddGroup.eq_zero_iff (N := walsh k) (chi s)).2 (AddMonoidHom.mem_range.2 ⟨s, rfl⟩),
    add_zero]
  exact QuotientAddGroup.out_eq' P

/-- Every function is `rep P + χ_s` for at most one pair `(P, s)`. -/
theorem rep_add_chi_injective : Function.Injective fun p : Cls k × Lab k ↦ rep p.1 + chi p.2 := by
  rintro ⟨P, s⟩ ⟨P', s'⟩ h
  have hP : P = P' := by
    rw [← mk_rep_add_chi P s, ← mk_rep_add_chi P' s']
    exact congrArg _ h
  subst hP
  simp only [add_right_inj] at h
  rw [chi_injective h]

/-- The classes are at most a `2^{-k}` fraction of the functions. -/
theorem card_cls_mul_le : Fintype.card (Cls k) * 2 ^ k ≤ Fintype.card (Fn k) := by
  have := Fintype.card_le_of_injective _ (rep_add_chi_injective (k := k))
  rwa [Fintype.card_prod, card_lab] at this

/-- There are `|Cls k| C(2^k, z)` left vertices. -/
theorem card_lft : Fintype.card (Lft k z) = Fintype.card (Cls k) * (2 ^ k).choose z := by
  have hN : Fintype.card (Pt k) = 2 ^ k := card_lab k
  rw [Fintype.card_prod, Fintype.card_finset_len, hN]

/-- Filtering the list of a finset counts the filtered finset. -/
theorem length_filter_toList' {α : Type*} (s : Finset α) (q : α → Bool) :
    (s.toList.filter q).length = #(s.filter fun a ↦ q a = true) := by
  rw [card_def, filter_val, ← coe_toList s, Multiset.filter_coe, Multiset.coe_card]
  simp

/-- The labels of the left vertices read off a labeling. -/
noncomputable def lLab (σ : Fin (Fintype.card (Lft k z)) → Fin (2 ^ k)) (u : Lft k z) : Lab k :=
  (labIdx k).symm (σ (lIdx k z u))

/-- The labels of the right vertices read off a labeling. -/
noncomputable def rLab (τ : Fin (Fintype.card (Cls k)) → Fin (2 ^ k)) (P : Cls k) : Lab k :=
  (labIdx k).symm (τ (rIdx k P))

/-- The set `A` of the functions `rep P + χ_{τ P}` chosen by a labeling of the right vertices. -/
noncomputable def chosen (τ : Fin (Fintype.card (Cls k)) → Fin (2 ^ k)) : Finset (Fn k) :=
  univ.image fun P ↦ rep P + chi (rLab τ P)

/-- `A` has one function in each class. -/
theorem card_chosen (τ : Fin (Fintype.card (Cls k)) → Fin (2 ^ k)) :
    #(chosen τ) = Fintype.card (Cls k) := by
  refine card_image_of_injective _ fun P P' h ↦ ?_
  have := rep_add_chi_injective (k := k) (a₁ := (P, rLab τ P)) (a₂ := (P', rLab τ P')) h
  exact congrArg Prod.fst this

/-- The table of the constraint of `e` at `u` sends the right label `t` to `t - κ`. -/
theorem table_getD' (u : Lft k z) (e : Fn k) (j : Fin (2 ^ k)) :
    (table u e).getD j 0 = (labIdx k ((labIdx k).symm j - kap u e) : ℕ) := by
  simp [table, List.getD_eq_getElem?_getD]

/-- **A satisfied constraint lands in `A`**: if the left label `s` of `u = (Q, Z)` satisfies the
constraint of `e`, then `rep Q + χ_s + e` is the chosen function `rep P + χ_{τ P}` of its class. -/
theorem mem_chosen_of_sat (σ : Fin (Fintype.card (Lft k z)) → Fin (2 ^ k))
    (τ : Fin (Fintype.card (Cls k)) → Fin (2 ^ k)) (u : Lft k z) (e : Fn k)
    (h : (σ (lIdx k z u) : ℕ) = (table u e).getD (τ (rIdx k (tgt u e)) : ℕ) 0) :
    rep u.1 + chi (lLab σ u) + e ∈ chosen τ := by
  rw [table_getD'] at h
  have hs : lLab σ u = rLab τ (tgt u e) - kap u e := by
    rw [lLab, Fin.ext h, Equiv.symm_apply_apply, rLab]
  have hk := kap_spec u e
  have hchi : chi (rLab τ (tgt u e) - kap u e) = chi (rLab τ (tgt u e)) - chi (kap u e) :=
    (chiHom k).map_sub _ _
  refine mem_image.2 ⟨tgt u e, mem_univ _, ?_⟩
  rw [hs, hchi, ← hk]
  abel

open Classical in
/-- The satisfied constraints are at most `Σ_{(Q, Z)} c_Z(rep Q + χ_s)`. -/
theorem sat_le (σ : Fin (Fintype.card (Lft k z)) → Fin (2 ^ k))
    (τ : Fin (Fintype.card (Cls k)) → Fin (2 ^ k)) :
    (ugSatisfied (kvInst k z)
      (fun n ↦ if h : n < Fintype.card (Lft k z) then (σ ⟨n, h⟩ : ℕ) else 0)
      (fun n ↦ if h : n < Fintype.card (Cls k) then (τ ⟨n, h⟩ : ℕ) else 0) : ℝ) ≤
      ∑ u : Lft k z, ∑ e with Supp u.2.1 e, ind (chosen τ) (rep u.1 + chi (lLab σ u) + e) := by
  simp only [ugSatisfied, kvInst, List.filter_map, List.length_map, edges]
  rw [length_filter_toList', natCast_card_filter]
  have hR : ∑ u : Lft k z, ∑ e with Supp u.2.1 e, ind (chosen τ) (rep u.1 + chi (lLab σ u) + e) =
      ∑ p : Lft k z × Fn k with Supp p.1.2.1 p.2,
        ind (chosen τ) (rep p.1.1 + chi (lLab σ p.1) + p.2) := by
    rw [sum_filter, Fintype.sum_prod_type (fun p : Lft k z × Fn k ↦
      if Supp p.1.2.1 p.2 then ind (chosen τ) (rep p.1.1 + chi (lLab σ p.1) + p.2) else 0)]
    exact sum_congr rfl fun u _ ↦ sum_filter _ _
  rw [hR]
  refine sum_le_sum fun p _ ↦ ?_
  split_ifs with hsat
  · refine le_of_eq (ite_eq_left (mem_chosen_of_sat σ τ p.1 p.2 ?_)).symm
    simp only [Function.comp_apply, decide_eq_true_eq] at hsat
    rwa [dite_eq_left (lIdx k z p.1).2, dite_eq_left (rIdx k _).2] at hsat
  · unfold ind; split_ifs <;> norm_num

open Classical in
/-- Every left vertex has `2^z` constraints. -/
theorem length_kvInst : ((kvInst k z).2.2.2.length : ℝ) = Fintype.card (Lft k z) * 2 ^ z := by
  simp only [kvInst, List.length_map, edges, length_toList]
  have h : #{p : Lft k z × Fn k | Supp p.1.2.1 p.2} =
      ∑ u : Lft k z, #{e : Fn k | Supp u.2.1 e} := by
    rw [card_filter, Fintype.sum_prod_type (fun p : Lft k z × Fn k ↦
      if Supp p.1.2.1 p.2 then 1 else 0)]
    exact sum_congr rfl fun u _ ↦ (card_filter _ _).symm
  rw [h, sum_congr rfl fun u _ ↦ by rw [card_suppFn, u.2.2]]
  simp

open Classical in
/-- **The left vertices are injected into the functions**: for each `Z`, the functions
`rep Q + χ_s` of the left vertices `(Q, Z)` are distinct. -/
theorem sum_sq_le_sum_sum_sq (A : Finset (Fn k)) (f : Lft k z → Fn k)
    (hf : ∀ Z, Function.Injective fun Q ↦ f (Q, Z)) :
    ∑ u : Lft k z, (∑ e with Supp u.2.1 e, ind A (f u + e)) ^ 2 ≤
      ∑ Z : {Z : Finset (Pt k) // #Z = z}, ∑ g : Fn k,
        (∑ e with Supp Z.1 e, ind A (g + e)) ^ 2 := by
  rw [Fintype.sum_prod_type (fun u : Lft k z ↦ (∑ e with Supp u.2.1 e, ind A (f u + e)) ^ 2),
    sum_comm]
  refine sum_le_sum fun Z _ ↦ ?_
  rw [← sum_image (s := univ) (g := fun Q ↦ f (Q, Z))
    (f := fun g ↦ (∑ e with Supp Z.1 e, ind A (g + e)) ^ 2) fun Q _ Q' _ h ↦ hf Z h]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ sq_nonneg _

/-- The arithmetic of the Cauchy–Schwarz step. -/
theorem sq_div_le {sat C M D B Ccls X : ℝ} (hCcls : 0 < Ccls) (hB : 0 < B) (hD : 0 < D)
    (hsat0 : 0 ≤ sat) (hsat : sat ≤ C) (hC : C ^ 2 ≤ Ccls * B * (M * D ^ 2 * B * X)) :
    (sat / (Ccls * B * D)) ^ 2 ≤ X / (Ccls / M) := by
  rw [div_div_eq_mul_div, div_pow, div_le_div_iff₀ (by positivity) hCcls]
  have h : sat ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ hsat0 hsat 2
  calc sat ^ 2 * Ccls ≤ Ccls * B * (M * D ^ 2 * B * X) * Ccls :=
        mul_le_mul_of_nonneg_right (h.trans hC) hCcls.le
    _ = X * M * (Ccls * B * D) ^ 2 := by ring

/-- The arithmetic of the exponent: `μ^{2/(1+ρ) - 1} ≤ 2^{-k η/4}` for `μ ≤ 2^{-k}`,
`ρ = 1 - η`, `η = z/2^k ≤ 1/4`. -/
theorem rpow_bound {μ v : ℝ} (hμ0 : 0 < μ) (hμ : μ * 2 ^ k ≤ 1) (hz : 4 * z ≤ 2 ^ k)
    (hv0 : 0 ≤ v) (hv : v ^ 2 ≤ μ ^ ((1 + (1 - (z : ℝ) / 2 ^ k))⁻¹ * 2) / μ) :
    v ≤ (2 : ℝ) ^ (-((k : ℝ) * z) / (8 * 2 ^ k)) := by
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  have hzN : 4 * (z : ℝ) ≤ 2 ^ k := by exact_mod_cast hz
  set η : ℝ := z / 2 ^ k with hη
  have hη0 : 0 ≤ η := by positivity
  have hη1 : η ≤ 1 / 4 := by
    rw [hη, div_le_iff₀ hN]; linarith
  rw [← Real.rpow_sub_one hμ0.ne'] at hv
  have hexp : η / 4 ≤ (1 + (1 - η))⁻¹ * 2 - 1 := by
    have h2 : 0 < 2 - η := by linarith
    rw [show (1 + (1 - η))⁻¹ * 2 - 1 = η / (2 - η) by
      rw [show 1 + (1 - η) = 2 - η by ring]; field_simp; ring]
    exact div_le_div_of_nonneg_left hη0 h2 (by linarith)
  have hN1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hμ1 : μ ≤ 1 := by nlinarith
  have hμ2 : μ ≤ (2 : ℝ) ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← one_div, le_div_iff₀ hN]
    exact hμ
  have h1 := Real.rpow_le_rpow_of_exponent_ge hμ0 hμ1 hexp
  have h2 := Real.rpow_le_rpow hμ0.le hμ2 (by positivity : 0 ≤ η / 4)
  have h3 : ((2 : ℝ) ^ (-(k : ℝ))) ^ (η / 4) =
      ((2 : ℝ) ^ (-((k : ℝ) * z) / (8 * 2 ^ k))) ^ 2 := by
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    rw [hη]; push_cast; field_simp; ring
  refine (pow_le_pow_iff_left₀ hv0 (by positivity) two_ne_zero).1 ?_
  linarith

open Classical in
/-- **Soundness for one labeling**. -/
theorem labeling_le (hz : 4 * z ≤ 2 ^ k) (σ : Fin (Fintype.card (Lft k z)) → Fin (2 ^ k))
    (τ : Fin (Fintype.card (Cls k)) → Fin (2 ^ k)) :
    (ugSatisfied (kvInst k z)
      (fun n ↦ if h : n < Fintype.card (Lft k z) then (σ ⟨n, h⟩ : ℕ) else 0)
      (fun n ↦ if h : n < Fintype.card (Cls k) then (τ ⟨n, h⟩ : ℕ) else 0) : ℝ) /
      (kvInst k z).2.2.2.length ≤ (2 : ℝ) ^ (-((k : ℝ) * z) / (8 * 2 ^ k)) := by
  have hz' : z ≤ 2 ^ k := by omega
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  have hρ0 : (0 : ℝ) ≤ 1 - z / 2 ^ k :=
    sub_nonneg.2 ((div_le_one hN).2 (by exact_mod_cast hz'))
  have hρ1 : (1 : ℝ) - z / 2 ^ k ≤ 1 := by
    have : (0 : ℝ) ≤ z / 2 ^ k := by positivity
    linarith
  have hinj : ∀ Z, Function.Injective fun Q : Cls k ↦ rep (Q, Z).1 + chi (lLab σ (Q, Z)) := by
    intro Z Q Q' h
    rw [← mk_rep_add_chi Q (lLab σ (Q, Z)), ← mk_rep_add_chi Q' (lLab σ (Q', Z))]
    exact congrArg _ h
  have h2 : (∑ u : Lft k z, ∑ e with Supp u.2.1 e,
        ind (chosen τ) (rep u.1 + chi (lLab σ u) + e)) ^ 2 ≤
      (Fintype.card (Lft k z) : ℝ) * ∑ u : Lft k z, (∑ e with Supp u.2.1 e,
        ind (chosen τ) (rep u.1 + chi (lLab σ u) + e)) ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Lft k z)))
      (f := fun u ↦ ∑ e with Supp u.2.1 e, ind (chosen τ) (rep u.1 + chi (lLab σ u) + e))
  have h3 := sum_sq_le_sum_sum_sq (chosen τ) (fun u ↦ rep u.1 + chi (lLab σ u)) hinj
  have h4 := sum_sum_sq_le (chosen τ) hz'
  have h5 := stab_le (chosen τ) hρ0 hρ1
  rw [card_chosen] at h5
  have hB : (0 : ℝ) < (2 ^ k).choose z := by exact_mod_cast Nat.choose_pos hz'
  have hC : (0 : ℝ) < Fintype.card (Cls k) := by exact_mod_cast Fintype.card_pos
  have hM : (0 : ℝ) < Fintype.card (Fn k) := by exact_mod_cast Fintype.card_pos
  have hL : (Fintype.card (Lft k z) : ℝ) = Fintype.card (Cls k) * (2 ^ k).choose z := by
    exact_mod_cast card_lft
  rw [hL] at h2
  rw [length_kvInst, hL]
  refine rpow_bound (μ := (Fintype.card (Cls k) : ℝ) / Fintype.card (Fn k)) (by positivity) ?_ hz
    (div_nonneg (Nat.cast_nonneg _) (by positivity)) ?_
  · rw [div_mul_eq_mul_div, div_le_one hM]
    exact_mod_cast card_cls_mul_le
  · refine sq_div_le hC hB (by positivity) (Nat.cast_nonneg _) (sat_le σ τ) (h2.trans ?_)
    refine mul_le_mul_of_nonneg_left (h3.trans (h4.trans ?_)) (by positivity)
    exact mul_le_mul_of_nonneg_left h5 (by positivity)

end BGHKLMM26.IntGap.Snd

namespace BGHKLMM26.IntGap

open UniqueGames

/-- **Soundness**: the value of `kvInst k z` is at most `2^{-k z / (8 · 2^k)}`. -/
theorem kvInst_value_le {k z : ℕ} (_hk : 1 ≤ k) (hz : 4 * z ≤ 2 ^ k) :
    ugValue (kvInst k z) ≤ (2 : ℝ) ^ (-((k : ℝ) * z) / (8 * 2 ^ k)) := by
  unfold ugValue
  exact Real.iSup_le (fun σ ↦ Real.iSup_le (fun τ ↦ Snd.labeling_le hz σ τ) (by positivity))
    (by positivity)

end BGHKLMM26.IntGap
