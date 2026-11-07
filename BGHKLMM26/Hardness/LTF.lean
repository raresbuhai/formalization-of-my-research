module

public import BGHKLMM26.Hardness.Defs

/-!
# Linear threshold functions

Facts about LTFs on the cube used by the soundness analysis of [BGHKLMM26, Sections 5–6]:

* **Counting** (`BGHKLMM26.Hard.card_ltf_le`): there are at most `(2^R + 1)^(R+1)` LTFs on
  `{0,1}^R`, by Chow's theorem (`BGHKLMM26.Hard.eq_of_chow`) — an LTF is determined among all
  Boolean functions by its `R + 1` Chow parameters `#{x : L x}` and `#{x : L x ∧ xᵢ}`: with a
  representation `L x = [ℓ(x) > 0]`, `ℓ(x) ≠ 0`, the sum `∑ₓ (L x - M x) ℓ(x)` vanishes and has
  nonnegative terms. This replaces the paper's appendix (VC dimension and Sauer–Shelah) and
  gives the same `2^O(R²)`.
* **The distance** `ltfDist` is attained (`BGHKLMM26.Hard.exists_ltfDist_eq`): there are finitely
  many LTFs, and the constants are LTFs.
* **Invariance** under permutations of the coordinates (Claim 4.7) and under flipping
  coordinates; in general under any bijection `E` of the cube that maps LTFs to LTFs both ways
  (`BGHKLMM26.Hard.ltfDist_comp_equiv`).
* **Averaging** (Lemma 4.8): `E dist(fⱼ, ℒ) ≤ dist(E fⱼ, ℒ)` for `[0,1]`-valued `fⱼ`, because
  `|a - L|` is affine in `a ∈ [0,1]` for `L ∈ {0,1}` (`BGHKLMM26.Hard.abs_sub_bitVal`).
* **Noise** as an average of shifts (`BGHKLMM26.Hard.noise_eq_sum`, with the flip law
  `flipWeight` nonnegative of mass `1` for `u ∈ [-1, 1]`), and Corollary 4.6:
  `dist(f, ℒ) ≤ dist(T_u f, ℒ)` for Boolean `f`.
-/

@[expose] public section

namespace BGHKLMM26.Hard

open Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic
  OAI.OptimalMaxCut.GaussianBellman

variable {R : ℕ}

/-! ### Counting -/

/-- Every LTF has a representation `L x = [θ < ℓ(x)]` with `ℓ(x) ≠ θ` for all `x`. -/
theorem IsLTF.exists_strict {L : Cube (Fin R) → Bool} (hL : IsLTF L) :
    ∃ (w : Fin R → ℝ) (θ : ℝ), ∀ x, (L x = true ↔ θ < ∑ i, w i * bitSign (x i)) ∧
      ∑ i, w i * bitSign (x i) ≠ θ := by
  obtain ⟨w, θ, hw⟩ := hL
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Cube (Fin R) → ℝ, ℓ = fun x ↦ ∑ i, w i * bitSign (x i) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Cube (Fin R) → ℝ, v = fun x ↦ if ℓ x < θ then (θ - ℓ x) / 2 else 1 :=
    ⟨_, rfl⟩
  have hvpos : ∀ x, 0 < v x := fun x ↦ by
    rw [hv]
    dsimp only
    split_ifs with h
    · linarith
    · exact one_pos
  obtain ⟨x₀, hx₀⟩ := Finite.exists_min v
  refine ⟨w, θ - v x₀, fun x ↦ ?_⟩
  have hx := hvpos x₀
  have hlx : ∑ i, w i * bitSign (x i) = ℓ x := by rw [hℓ]
  rw [hw x, decide_eq_true_iff, hlx]
  by_cases h : θ ≤ ℓ x
  · exact ⟨iff_of_true h (by linarith), by linarith⟩
  · replace h := not_le.1 h
    have h' : v x₀ ≤ (θ - ℓ x) / 2 := by
      have := hx₀ x
      rw [hv] at this ⊢
      simpa [h] using this
    exact ⟨iff_of_false (by linarith) (by linarith), by linarith⟩

/-- The Chow parameter `#{x : M x}`. -/
noncomputable def chow0 (M : Cube (Fin R) → Bool) : ℕ := (univ.filter fun x ↦ M x = true).card

/-- The Chow parameter `#{x : M x ∧ xᵢ}`. -/
noncomputable def chowI (M : Cube (Fin R) → Bool) (i : Fin R) : ℕ :=
  (univ.filter fun x ↦ (M x && x i) = true).card

theorem sum_bitVal (M : Cube (Fin R) → Bool) : ∑ x, bitVal (M x) = chow0 M := by
  simp [bitVal, Finset.sum_boole, chow0]

theorem sum_bitVal_mul_bitSign (M : Cube (Fin R) → Bool) (i : Fin R) :
    ∑ x, bitVal (M x) * bitSign (x i) = chow0 M - 2 * chowI M i := by
  have e : ∀ x : Cube (Fin R), bitVal (M x) * bitSign (x i) =
      bitVal (M x) - 2 * bitVal (M x && x i) := fun x ↦ by
    cases M x <;> cases x i <;> norm_num [bitVal, bitSign]
  simp_rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_bitVal]
  rfl

theorem sum_bitVal_mul_affine (M : Cube (Fin R) → Bool) (w : Fin R → ℝ) (θ : ℝ) :
    ∑ x, bitVal (M x) * (∑ i, w i * bitSign (x i) - θ) =
      ∑ i, w i * (chow0 M - 2 * chowI M i) - θ * chow0 M := by
  simp_rw [← sum_bitVal_mul_bitSign, ← sum_bitVal, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
    ring
  · exact Finset.sum_congr rfl fun x _ ↦ mul_comm _ _

/-- **Chow's theorem**: an LTF is determined among all Boolean functions by its Chow
parameters. -/
theorem eq_of_chow {L M : Cube (Fin R) → Bool} (hL : IsLTF L) (h0 : chow0 M = chow0 L)
    (hi : ∀ i, chowI M i = chowI L i) : M = L := by
  obtain ⟨w, θ, hw⟩ := hL.exists_strict
  have hD : ∑ x, (bitVal (L x) - bitVal (M x)) * (∑ i, w i * bitSign (x i) - θ) = 0 := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, sum_bitVal_mul_affine, h0, hi, sub_self]
  have hnn : ∀ x, 0 ≤ (bitVal (L x) - bitVal (M x)) * (∑ i, w i * bitSign (x i) - θ) := by
    intro x
    obtain ⟨h1, h2⟩ := hw x
    cases hLx : L x <;> cases hMx : M x <;> simp only [bitVal] <;> norm_num
    · rw [hLx] at h1
      have : ¬ θ < ∑ i, w i * bitSign (x i) := fun h ↦ absurd (h1.2 h) (by simp)
      linarith
    · rw [hLx] at h1
      linarith [h1.1 rfl]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun x _ ↦ hnn x).1 hD
  funext x
  have hx := hz x (Finset.mem_univ x)
  rcases mul_eq_zero.1 hx with h | h
  · cases hLx : L x <;> cases hMx : M x <;> simp_all [bitVal]
  · exact absurd (sub_eq_zero.1 h) (hw x).2

theorem card_filter_le_pow (p : Cube (Fin R) → Prop) [DecidablePred p] :
    (univ.filter p).card ≤ 2 ^ R := by
  refine (Finset.card_filter_le _ _).trans_eq ?_
  simp

/-- The Chow parameters of a function, in `[0, 2^R]`. -/
noncomputable def chowMap (L : Cube (Fin R) → Bool) : Fin (2 ^ R + 1) × (Fin R → Fin (2 ^ R + 1)) :=
  (⟨chow0 L, Nat.lt_succ_of_le (card_filter_le_pow _)⟩,
    fun i ↦ ⟨chowI L i, Nat.lt_succ_of_le (card_filter_le_pow _)⟩)

/-- **The number of LTFs** on `{0,1}^R` is at most `(2^R + 1)^(R+1)`. -/
theorem card_ltf_le (R : ℕ) :
    Nat.card {L : Cube (Fin R) → Bool // IsLTF L} ≤ (2 ^ R + 1) ^ (R + 1) := by
  have hinj : Function.Injective fun L : {L : Cube (Fin R) → Bool // IsLTF L} ↦ chowMap L.1 := by
    rintro ⟨L, hL⟩ ⟨M, hM⟩ h
    simp only [chowMap, Prod.mk.injEq, Fin.mk.injEq, funext_iff] at h
    exact Subtype.ext (eq_of_chow hL h.1.symm fun i ↦ (h.2 i).symm).symm
  refine (Nat.card_le_card_of_injective _ hinj).trans_eq ?_
  simp [pow_succ, mul_comm]

/-! ### The distance to the LTFs -/

theorem isLTF_const (R : ℕ) (b : Bool) : IsLTF (fun _ : Cube (Fin R) ↦ b) := by
  refine ⟨0, if b then 0 else 1, fun x ↦ ?_⟩
  cases b <;> simp

instance instNonemptyLTF (R : ℕ) : Nonempty {L : Cube (Fin R) → Bool // IsLTF L} :=
  ⟨⟨_, isLTF_const R true⟩⟩

theorem ltfDist_le (g : Cube (Fin R) → ℝ) {L : Cube (Fin R) → Bool} (hL : IsLTF L) :
    ltfDist g ≤ 𝔼 x, |g x - bitVal (L x)| :=
  ciInf_le (Set.finite_range _).bddBelow (⟨L, hL⟩ : {L : Cube (Fin R) → Bool // IsLTF L})

/-- The distance is attained. -/
theorem exists_ltfDist_eq (g : Cube (Fin R) → ℝ) :
    ∃ L : Cube (Fin R) → Bool, IsLTF L ∧ 𝔼 x, |g x - bitVal (L x)| = ltfDist g := by
  obtain ⟨⟨L, hL⟩, h⟩ := Finite.ciInf_mem
    (fun L : {L : Cube (Fin R) → Bool // IsLTF L} ↦ 𝔼 x, |g x - bitVal (L.1 x)|)
  exact ⟨L, hL, h⟩

theorem ltfDist_nonneg (g : Cube (Fin R) → ℝ) : 0 ≤ ltfDist g := by
  obtain ⟨L, -, h⟩ := exists_ltfDist_eq g
  rw [← h]
  exact Finset.expect_nonneg fun x _ ↦ abs_nonneg _

/-! ### Invariance -/

/-- A table `π` of a permutation of `[R]`. -/
def IsPermTable (R : ℕ) (π : List ℕ) : Prop := π.length = R ∧ π.Nodup ∧ ∀ a ∈ π, a < R

/-- If `L ∘ E` is an LTF for every LTF `L`, composing with `E` does not increase the distance. -/
theorem ltfDist_comp_equiv_le (E : Cube (Fin R) ≃ Cube (Fin R))
    (hE : ∀ L : Cube (Fin R) → Bool, IsLTF L → IsLTF (fun x ↦ L (E x))) (g : Cube (Fin R) → ℝ) :
    ltfDist (fun x ↦ g (E x)) ≤ ltfDist g := by
  obtain ⟨L, hL, hLd⟩ := exists_ltfDist_eq g
  rw [← hLd]
  refine (ltfDist_le _ (hE L hL)).trans_eq ?_
  exact Fintype.expect_equiv E _ _ fun _ ↦ rfl

theorem ltfDist_comp_equiv (E : Cube (Fin R) ≃ Cube (Fin R))
    (hE : ∀ L : Cube (Fin R) → Bool, IsLTF L → IsLTF (fun x ↦ L (E x)))
    (hE' : ∀ L : Cube (Fin R) → Bool, IsLTF L → IsLTF (fun x ↦ L (E.symm x)))
    (g : Cube (Fin R) → ℝ) :
    ltfDist (fun x ↦ g (E x)) = ltfDist g := by
  refine le_antisymm (ltfDist_comp_equiv_le E hE g) ?_
  have h := ltfDist_comp_equiv_le E.symm hE' (fun x ↦ g (E x))
  simpa using h

/-- Flipping coordinates maps LTFs to LTFs. -/
theorem isLTF_comp_xor {L : Cube (Fin R) → Bool} (hL : IsLTF L) (z : Cube (Fin R)) :
    IsLTF (fun x ↦ L (cubeXor x z)) := by
  obtain ⟨w, θ, hw⟩ := hL
  refine ⟨fun i ↦ w i * bitSign (z i), θ, fun x ↦ ?_⟩
  dsimp only
  rw [hw]
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [cubeXor, bitSign_xor]
  ring

/-- Permuting coordinates maps LTFs to LTFs. -/
theorem isLTF_comp_perm {L : Cube (Fin R) → Bool} (hL : IsLTF L) (e : Fin R ≃ Fin R) :
    IsLTF (fun x ↦ L (fun j ↦ x (e j))) := by
  obtain ⟨w, θ, hw⟩ := hL
  refine ⟨fun i ↦ w (e.symm i), θ, fun x ↦ ?_⟩
  dsimp only
  rw [hw]
  congr 2
  exact (Equiv.sum_comp e.symm (fun i ↦ w i * bitSign (x (e i)))).symm.trans (by simp)

/-- The shift `x ↦ x ⊕ z`, an involution of the cube. -/
def xorEquiv (z : Cube (Fin R)) : Cube (Fin R) ≃ Cube (Fin R) where
  toFun x := cubeXor x z
  invFun x := cubeXor x z
  left_inv x := by funext i; simp [cubeXor]
  right_inv x := by funext i; simp [cubeXor]

theorem expect_cubeXor (z : Cube (Fin R)) (f : Cube (Fin R) → ℝ) :
    𝔼 x, f (cubeXor x z) = 𝔼 x, f x :=
  Fintype.expect_equiv (xorEquiv z) _ _ fun _ ↦ rfl

theorem list_getD_eq_getElem {l : List ℕ} {n : ℕ} (hn : n < l.length) : l.getD n 0 = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]

/-- The coordinate map of a permutation table. -/
def permTableFun {π : List ℕ} (hπ : IsPermTable R π) (j : Fin R) : Fin R :=
  ⟨π.getD j 0, by
    rw [list_getD_eq_getElem (hπ.1 ▸ j.2)]
    exact hπ.2.2 _ (List.getElem_mem _)⟩

theorem permTableFun_injective {π : List ℕ} (hπ : IsPermTable R π) :
    Function.Injective (permTableFun hπ) := by
  intro i j hij
  simp only [permTableFun, Fin.mk.injEq] at hij
  rw [list_getD_eq_getElem (hπ.1 ▸ i.2), list_getD_eq_getElem (hπ.1 ▸ j.2)] at hij
  exact Fin.ext ((hπ.2.1.getElem_inj_iff).1 hij)

/-- The permutation of `[R]` given by a table. -/
noncomputable def permTableEquiv {π : List ℕ} (hπ : IsPermTable R π) : Fin R ≃ Fin R :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (permTableFun_injective hπ))

theorem permCube_eq {π : List ℕ} (hπ : IsPermTable R π) (x : Cube (Fin R)) :
    permCube π x = fun j ↦ x (permTableEquiv hπ j) := by
  funext j
  have h : π.getD j 0 < R := (permTableFun hπ j).2
  simp only [permCube, h, dite_true]
  rfl

/-- `x ↦ π x` as a bijection of the cube. -/
noncomputable def permCubeEquiv {π : List ℕ} (hπ : IsPermTable R π) :
    Cube (Fin R) ≃ Cube (Fin R) :=
  (permTableEquiv hπ).symm.arrowCongr (Equiv.refl Bool)

theorem permCubeEquiv_apply {π : List ℕ} (hπ : IsPermTable R π) (x : Cube (Fin R)) :
    permCubeEquiv hπ x = permCube π x := by
  rw [permCube_eq hπ]
  rfl

/-- **Claim 4.7**: permuting the coordinates does not change the distance to the LTFs. -/
theorem ltfDist_comp_permCube {π : List ℕ} (hπ : IsPermTable R π) (g : Cube (Fin R) → ℝ) :
    ltfDist (fun x ↦ g (permCube π x)) = ltfDist g := by
  have h := ltfDist_comp_equiv (permCubeEquiv hπ) (fun L hL ↦ ?_) (fun L hL ↦ ?_) g
  · simpa only [permCubeEquiv_apply] using h
  · simp only [permCubeEquiv_apply, permCube_eq hπ]
    exact isLTF_comp_perm hL _
  · exact isLTF_comp_perm hL (permTableEquiv hπ).symm

/-! ### Averaging -/

/-- `|a - L|` for `a ∈ [0,1]` and `L ∈ {0,1}`, an affine function of `a`. -/
theorem abs_sub_bitVal {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (c : Bool) :
    |a - bitVal c| = if c then 1 - a else a := by
  cases c
  · simp [bitVal, abs_of_nonneg ha0]
  · simp [bitVal, abs_of_nonpos (sub_nonpos.2 ha1), neg_sub]

theorem list_sum_map_expect {ι : Type*} (l : List ι) (F : ι → Cube (Fin R) → ℝ) :
    (l.map fun j ↦ 𝔼 x, F j x).sum = 𝔼 x, (l.map fun j ↦ F j x).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp [ih, Finset.expect_add_distrib]

theorem list_sum_map_one_sub {ι : Type*} (l : List ι) (a : ι → ℝ) :
    (l.map fun j ↦ 1 - a j).sum = l.length - (l.map a).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp [ih]; ring

/-- The average of `[0,1]`-values is in `[0,1]`. -/
theorem list_avg_mem {ι : Type*} (l : List ι) (hl : l ≠ []) (a : ι → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1) :
    0 ≤ (l.map a).sum / l.length ∧ (l.map a).sum / l.length ≤ 1 := by
  have hn : (0 : ℝ) < l.length := by exact_mod_cast List.length_pos_iff.2 hl
  have h0 : 0 ≤ (l.map a).sum := List.sum_nonneg (by
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun j _ ↦ (ha j).1)
  have h1 : 0 ≤ (l.map fun j ↦ 1 - a j).sum :=
    List.sum_nonneg (by
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, sub_nonneg]
      exact fun j _ ↦ (ha j).2)
  rw [list_sum_map_one_sub] at h1
  refine ⟨div_nonneg h0 hn.le, (div_le_one hn).2 (by linarith)⟩

theorem list_avg_abs_sub_bitVal {ι : Type*} (l : List ι) (hl : l ≠ []) (a : ι → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1) (c : Bool) :
    (l.map fun j ↦ |a j - bitVal c|).sum / l.length = |(l.map a).sum / l.length - bitVal c| := by
  have hn : (l.length : ℝ) ≠ 0 := by exact_mod_cast (List.length_pos_iff.2 hl).ne'
  obtain ⟨h0, h1⟩ := list_avg_mem l hl a ha
  rw [abs_sub_bitVal h0 h1]
  have e : (l.map fun j ↦ |a j - bitVal c|) = l.map fun j ↦ if c then 1 - a j else a j :=
    List.map_congr_left fun j _ ↦ abs_sub_bitVal (ha j).1 (ha j).2 c
  rw [e]
  cases c
  · simp
  · simp only [ite_true]
    rw [list_sum_map_one_sub]
    field_simp

/-- **Lemma 4.8**: for `[0,1]`-valued functions, the average distance to the LTFs is at most the
distance of the average. -/
theorem avg_ltfDist_le {ι : Type*} (l : List ι) (hl : l ≠ []) (h : ι → Cube (Fin R) → ℝ)
    (hh : ∀ j x, 0 ≤ h j x ∧ h j x ≤ 1) :
    (l.map fun j ↦ ltfDist (h j)).sum / l.length ≤
      ltfDist (fun x ↦ (l.map fun j ↦ h j x).sum / l.length) := by
  have hn : (0 : ℝ) < l.length := by exact_mod_cast List.length_pos_iff.2 hl
  obtain ⟨L, hL, hLd⟩ := exists_ltfDist_eq (fun x ↦ (l.map fun j ↦ h j x).sum / l.length)
  rw [← hLd]
  simp_rw [← list_avg_abs_sub_bitVal l hl (fun j ↦ h _ _) (fun j ↦ hh j _), ← Finset.expect_div,
    ← list_sum_map_expect]
  gcongr
  exact List.sum_le_sum fun j _ ↦ ltfDist_le _ hL

/-! ### Noise -/

/-- The law of the flips of `T_u`: each coordinate flips with probability `(1 - u)/2`. -/
noncomputable def flipWeight (u : ℝ) (z : Cube (Fin R)) : ℝ :=
  ∏ i, if z i then (1 - u) / 2 else (1 + u) / 2

theorem flipWeight_eq (u : ℝ) (x z : Cube (Fin R)) :
    (∏ i, (1 + u * bitSign (cubeXor x z i) * bitSign (x i))) / (Fintype.card (Cube (Fin R)) : ℝ) =
      flipWeight u z := by
  have hc : (Fintype.card (Cube (Fin R)) : ℝ) = ∏ _i : Fin R, (2 : ℝ) := by
    simp
  rw [hc, ← Finset.prod_div_distrib, flipWeight]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp only [cubeXor]
  cases x i <;> cases z i <;> simp [bitSign] <;> ring

/-- **The noise operator as an average of shifts**: `T_u f(x) = E f(x ⊕ z)` over `(1-u)/2`-biased
`z`. -/
theorem noise_eq_sum (u : ℝ) (f : Cube (Fin R) → ℝ) (x : Cube (Fin R)) :
    noise u f x = ∑ z, flipWeight u z * f (cubeXor x z) := by
  rw [noise_kernel, ← Fintype.expect_equiv (xorEquiv x) (fun z ↦ f (cubeXor x z) *
    ∏ i, (1 + u * bitSign (cubeXor x z i) * bitSign (x i))) _ (fun z ↦ ?_),
    Fintype.expect_eq_sum_div_card, Finset.sum_div]
  · refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [mul_div_assoc, flipWeight_eq, mul_comm]
  · have : xorEquiv x z = cubeXor x z := by
      change cubeXor z x = cubeXor x z
      funext i; simp [cubeXor, Bool.xor_comm]
    rw [this]

theorem flipWeight_nonneg {u : ℝ} (hu0 : -1 ≤ u) (hu1 : u ≤ 1) (z : Cube (Fin R)) :
    0 ≤ flipWeight u z :=
  Finset.prod_nonneg fun i _ ↦ by split_ifs <;> linarith

theorem sum_flipWeight (u : ℝ) : ∑ z : Cube (Fin R), flipWeight u z = 1 := by
  have h := noise_eq_sum u (fun _ : Cube (Fin R) ↦ (1 : ℝ)) (fun _ ↦ false)
  rw [noise_one] at h
  simpa using h.symm

theorem noise_mem {u : ℝ} (hu0 : -1 ≤ u) (hu1 : u ≤ 1) {f : Cube (Fin R) → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : Cube (Fin R)) : 0 ≤ noise u f x ∧ noise u f x ≤ 1 := by
  rw [noise_eq_sum]
  constructor
  · exact Finset.sum_nonneg fun z _ ↦
      mul_nonneg (flipWeight_nonneg hu0 hu1 z) (hf _).1
  · calc ∑ z, flipWeight u z * f (cubeXor x z) ≤ ∑ z, flipWeight u z * 1 :=
          Finset.sum_le_sum fun z _ ↦
            mul_le_mul_of_nonneg_left (hf _).2 (flipWeight_nonneg hu0 hu1 z)
      _ = 1 := by simpa using sum_flipWeight u

/-- **Corollary 4.6**: for Boolean `f`, `dist(f, ℒ) ≤ dist(T_u f, ℒ)`. -/
theorem ltfDist_le_noise {u : ℝ} (hu0 : -1 ≤ u) (hu1 : u ≤ 1) (F : Cube (Fin R) → Bool) :
    ltfDist (fun x ↦ bitVal (F x)) ≤ ltfDist (noise u fun x ↦ bitVal (F x)) := by
  have hF : ∀ x, 0 ≤ bitVal (F x) ∧ bitVal (F x) ≤ 1 := fun x ↦ by
    cases F x <;> simp [bitVal]
  obtain ⟨L, hL, hLd⟩ := exists_ltfDist_eq (noise u fun x ↦ bitVal (F x))
  rw [← hLd]
  -- pointwise: `|T f x - L x| = ∑_z w(z) |f(x ⊕ z) - L x|`
  have hpt : ∀ x, |noise u (fun x ↦ bitVal (F x)) x - bitVal (L x)| =
      ∑ z, flipWeight u z * |bitVal (F (cubeXor x z)) - bitVal (L x)| := by
    intro x
    obtain ⟨h0, h1⟩ := noise_mem hu0 hu1 hF x
    rw [abs_sub_bitVal h0 h1]
    simp_rw [abs_sub_bitVal (hF _).1 (hF _).2]
    rw [noise_eq_sum]
    cases L x
    · simp
    · simp only [ite_true, mul_sub, mul_one, Finset.sum_sub_distrib, sum_flipWeight]
  simp_rw [hpt]
  rw [Finset.expect_sum_comm]
  calc ltfDist (fun x ↦ bitVal (F x))
      = ∑ z : Cube (Fin R), flipWeight u z * ltfDist (fun x ↦ bitVal (F x)) := by
        rw [← Finset.sum_mul, sum_flipWeight, one_mul]
    _ ≤ ∑ z, 𝔼 x, flipWeight u z * |bitVal (F (cubeXor x z)) - bitVal (L x)| := by
        refine Finset.sum_le_sum fun z _ ↦ ?_
        rw [← Finset.mul_expect]
        refine mul_le_mul_of_nonneg_left ?_ (flipWeight_nonneg hu0 hu1 z)
        rw [← expect_cubeXor z]
        have e : ∀ x : Cube (Fin R), cubeXor (cubeXor x z) z = x := fun x ↦ by
          funext i; simp [cubeXor]
        simp only [e]
        exact ltfDist_le _ (isLTF_comp_xor hL z)

end BGHKLMM26.Hard
