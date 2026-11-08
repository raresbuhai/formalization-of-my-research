module

public import BB20.Learning.Progress

/-!
# Comparing proxies: Lemma 28 and conditioning on one more variable

Two comparisons of the proxy `ν`, used by the pruning step of Theorem 11.

* `BB20.Learning.nu_le_of_nbhd` ([BB20, Lemma 28]): if `N(u) ⊆ Y ∪ S`, then
  `2^{|Z|} ν_{u,Z|S} ≤ 2^{|Y|} ν_{u,Y|S}`, since `m_{Z ∪ S} - m_S` is the conditional expectation
  of `m_{Y ∪ S} - m_S` given `X_{Z ∪ S}`.
* `BB20.Learning.nu_le_nu_insert`: conditioning on one more variable `i` changes the proxy of a
  set `Y` with `N(u) ⊆ Y ∪ S` by at most a factor `1 + 2 δ^{-|Y|}`:
  `ν_{u,Y|S} ≤ (1 + 2 δ^{-|Y|}) ν_{u,Y|S ∪ {i}}`. The point: `m_{S ∪ {i}}` can depend on `x_i`
  only through the law of `X_Y` given `X_{S ∪ {i}}`, whose probabilities are at least `δ^{|Y|}`,
  so the change is paid for by the variation of `m_{Y ∪ S}` around `m_{S ∪ {i}}`.
* `BB20.Learning.nu_le_of_notMem_nbhd`: the two together, for a non-neighbour `i`.
-/

@[expose] public section

namespace BB20.Learning

open Finset

variable {n m : ℕ} (R : RBM n m)

theorem notMem_nbhd_self (u : Fin n) : u ∉ R.nbhd u := by
  simp [RBM.nbhd]

/-- If `N(u) ⊆ Y ∪ S`, then `E|m_{Z ∪ S} - m_S| ≤ E|m_{Y ∪ S} - m_S|`. -/
theorem expect_abs_le_of_nbhd {u : Fin n} {Z Y S : Finset (Fin n)} (hZ : u ∉ Z ∪ S)
    (hY : u ∉ Y ∪ S) (hN : R.nbhd u ⊆ Y ∪ S) :
    expect R (fun x ↦ |mu R u (Z ∪ S) x - mu R u S x|) ≤
      expect R (fun x ↦ |mu R u (Y ∪ S) x - mu R u S x|) := by
  have hu : u ∉ Z ∪ (Y ∪ S) := by
    simp only [mem_union, not_or] at hZ hY ⊢
    exact ⟨hZ.1, hY.1, hY.2⟩
  have hg : mu R u (Y ∪ S) = mu R u (Z ∪ (Y ∪ S)) :=
    (mu_eq_of_nbhd R subset_union_right hN hu).symm
  have hsub : Z ∪ S ⊆ Z ∪ (Y ∪ S) := union_subset_union le_rfl subset_union_right
  have h1 : ∀ x, mu R u (Z ∪ S) x - mu R u S x =
      condExp R (Z ∪ S) (fun y ↦ mu R u (Y ∪ S) y - mu R u S y) x := by
    intro x
    rw [condExp_sub, hg]
    simp only [mu]
    rw [condExp_condExp R hsub,
      condExp_of_dep R (Z ∪ S) ((dep_condExp R S _).mono subset_union_right)]
  calc expect R (fun x ↦ |mu R u (Z ∪ S) x - mu R u S x|)
      ≤ expect R (condExp R (Z ∪ S) (fun y ↦ |mu R u (Y ∪ S) y - mu R u S y|)) :=
        expect_mono R fun x ↦ by rw [h1]; exact abs_condExp_le R _ _ x
    _ = _ := expect_condExp R _ _

theorem two_pow_mul_div (a : ℝ) (k : ℕ) : (2 : ℝ) ^ k * (a / 2 ^ k) = a := by
  field_simp

/-- **Lemma 28** of [BB20]: if `N(u) ⊆ Y ∪ S`, then `2^{|Z|} ν_{u,Z|S} ≤ 2^{|Y|} ν_{u,Y|S}`. -/
theorem nu_le_of_nbhd {u : Fin n} {Z Y S : Finset (Fin n)} (hZ : u ∉ Z ∪ S) (hY : u ∉ Y ∪ S)
    (hZS : Disjoint Z S) (hYS : Disjoint Y S) (hN : R.nbhd u ⊆ Y ∪ S) :
    2 ^ (Z.card + 1) * R.nu u Z S ≤ 2 ^ (Y.card + 1) * R.nu u Y S := by
  rw [nu_eq R u hZS, nu_eq R u hYS, two_pow_mul_div, two_pow_mul_div]
  exact expect_abs_le_of_nbhd R hZ hY hN

/-! ### Conditioning on one more variable -/

theorem condNum_split {i : Fin n} {A : Finset (Fin n)} (hi : i ∉ A) (h : Config n → ℝ)
    (z : Config n) :
    condNum R A h z = condNum R (insert i A) h z + condNum R (insert i A) h (flipAt i z) := by
  simp only [condNum, ← sum_add_distrib]
  refine sum_congr rfl fun y _ ↦ ?_
  simp only [forall_mem_insert]
  have hf : ∀ j ∈ A, flipAt i z j = z j := fun j hj ↦ flipAt_of_ne (ne_of_mem_of_not_mem hj hi) z
  have e : (∀ j ∈ A, y j = flipAt i z j) ↔ (∀ j ∈ A, y j = z j) :=
    forall₂_congr fun j hj ↦ by rw [hf j hj]
  rw [flipAt_self]
  simp only [e]
  by_cases hA : ∀ j ∈ A, y j = z j
  · simp only [and_iff_left hA]
    rw [ite_eq_left hA]
    cases y i <;> cases z i <;> simp
  · simp [hA]

theorem marg_split {i : Fin n} {A : Finset (Fin n)} (hi : i ∉ A) (z : Config n) :
    R.marg A z = R.marg (insert i A) z + R.marg (insert i A) (flipAt i z) := by
  rw [← condNum_one, ← condNum_one, ← condNum_one]
  exact condNum_split R hi _ z

/-- Conditioning on one more variable `i`: if `g` depends only on `Y ∪ S`, with `Y` disjoint
from `S ∪ {i}`, then `E|m_{S ∪ {i}} - m_S| ≤ 2 δ^{-|Y|} E|g - m_{S ∪ {i}}|`. -/
theorem expect_abs_mu_insert_le {γ : ℝ} (hW : R.WidthLE γ) {u i : Fin n}
    {S Y : Finset (Fin n)} (hi : i ∉ S) (hYS : Disjoint Y (insert i S)) (g : Config n → ℝ)
    (hg : Dep (Y ∪ S) g) :
    expect R (fun x ↦ |mu R u (insert i S) x - mu R u S x|) ≤
      2 / condLB γ ^ Y.card * expect R (fun x ↦ |g x - mu R u (insert i S) x|) := by
  set S₁ := insert i S with hS₁
  set c : Config n → ℝ := fun z ↦ R.marg S₁ z * R.marg S₁ (flipAt i z) / R.marg S z with hc
  have hiY : i ∉ Y := fun h ↦ disjoint_left.1 hYS h (mem_insert_self i S)
  -- the conditional expectation given `S` mixes those given `S ∪ {i}`
  have hid : ∀ z, R.marg S₁ z * |mu R u S₁ z - mu R u S z| =
      c z * |mu R u S₁ z - mu R u S₁ (flipAt i z)| := by
    intro z
    have ha := marg_pos R S₁ z
    have hb := marg_pos R S₁ (flipAt i z)
    have hN := condNum_split R hi (fun y ↦ spin (y u)) z
    have hM := marg_split R hi z
    simp only [mu, condExp, hc]
    rw [hN, hM]
    set a := R.marg S₁ z
    set b := R.marg S₁ (flipAt i z)
    set N := condNum R S₁ (fun y ↦ spin (y u)) z
    set N' := condNum R S₁ (fun y ↦ spin (y u)) (flipAt i z)
    rw [show N / a - (N + N') / (a + b) = b / (a + b) * (N / a - N' / b) by field_simp; ring,
      abs_mul, abs_of_pos (by positivity : 0 < b / (a + b))]
    ring
  have hcflip : ∀ z, c (flipAt i z) = c z := by
    intro z
    simp only [hc, flipAt_flipAt]
    rw [marg_congr R S (z := flipAt i z) (z' := z)
      fun j hj ↦ flipAt_of_ne (ne_of_mem_of_not_mem hj hi) z, mul_comm (R.marg S₁ (flipAt i z))]
  have hgflip : ∀ z, g (flipAt i z) = g z := by
    intro z
    refine hg _ _ fun j hj ↦ flipAt_of_ne ?_ z
    rintro rfl
    rcases mem_union.1 hj with h | h
    · exact hiY h
    · exact hi h
  have hc_nonneg : ∀ z, 0 ≤ c z := fun z ↦ by
    have := marg_pos R S₁ z
    have := marg_pos R S₁ (flipAt i z)
    have := marg_pos R S z
    simp only [hc]
    positivity
  have hc_le : ∀ z, c z ≤ R.marg S₁ z := fun z ↦ by
    have ha := marg_pos R S₁ z
    have hb := marg_pos R S₁ (flipAt i z)
    simp only [hc]
    rw [marg_split R hi z, div_le_iff₀ (by positivity)]
    nlinarith
  have hδ : 0 < condLB γ ^ Y.card := pow_pos (condLB_pos γ) _
  have hge : ∀ z, R.marg S₁ z ≤ R.marg (Y ∪ S₁) z / condLB γ ^ Y.card := fun z ↦ by
    have := R.marg_ge hW Y S₁ z
    rw [sdiff_eq_self_of_disjoint hYS] at this
    rw [le_div_iff₀ hδ]
    linarith
  -- the involution `flipAt i`
  have hsumflip : ∀ F : Config n → ℝ, ∑ z, F (flipAt i z) = ∑ z, F z := fun F ↦
    Equiv.sum_comp (Function.Involutive.toPerm (flipAt i) (flipAt_involutive i)) F
  set F : Config n → ℝ := fun z ↦ |g z - mu R u S₁ z| with hF
  have hmain : ∑ z, R.marg S₁ z * |mu R u S₁ z - mu R u S z| ≤
      2 / condLB γ ^ Y.card * ∑ z, R.marg (Y ∪ S₁) z * F z := by
    calc ∑ z, R.marg S₁ z * |mu R u S₁ z - mu R u S z|
        = ∑ z, c z * |mu R u S₁ z - mu R u S₁ (flipAt i z)| := sum_congr rfl fun z _ ↦ hid z
      _ ≤ ∑ z, (c z * F z + c (flipAt i z) * F (flipAt i z)) := by
          refine sum_le_sum fun z _ ↦ ?_
          rw [hcflip, ← mul_add]
          refine mul_le_mul_of_nonneg_left ?_ (hc_nonneg z)
          simp only [hF]
          rw [hgflip]
          calc |mu R u S₁ z - mu R u S₁ (flipAt i z)|
              ≤ |mu R u S₁ z - g z| + |g z - mu R u S₁ (flipAt i z)| := abs_sub_le _ _ _
            _ = _ := by rw [abs_sub_comm]
      _ = 2 * ∑ z, c z * F z := by
          rw [sum_add_distrib, hsumflip fun z ↦ c z * F z]
          ring
      _ ≤ 2 * ∑ z, R.marg (Y ∪ S₁) z / condLB γ ^ Y.card * F z := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun z _ ↦ ?_) (by norm_num)
          exact mul_le_mul_of_nonneg_right ((hc_le z).trans (hge z)) (abs_nonneg _)
      _ = 2 / condLB γ ^ Y.card * ∑ z, R.marg (Y ∪ S₁) z * F z := by
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun z _ ↦ ?_
          ring
  have hdepL : Dep S₁ fun x ↦ |mu R u S₁ x - mu R u S x| :=
    (dep_mu R u S₁).comp₂ ((dep_mu R u S).mono (subset_insert i S)) (fun a b ↦ |a - b|)
  have hdepR : Dep (Y ∪ S₁) F :=
    (hg.mono (union_subset_union le_rfl (subset_insert i S))).comp₂
      ((dep_mu R u S₁).mono subset_union_right) (fun a b ↦ |a - b|)
  rw [sum_marg_mul R S₁ _ hdepL, sum_marg_mul R (Y ∪ S₁) _ hdepR] at hmain
  have hpow : (2 : ℝ) ^ (n - (Y ∪ S₁).card) ≤ 2 ^ (n - S₁.card) :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_left (card_le_card subset_union_right) n)
  have hE : 0 ≤ expect R F := expect_nonneg R fun _ ↦ abs_nonneg _
  have hpos : (0 : ℝ) < 2 ^ (n - S₁.card) := by positivity
  have h2 : 0 ≤ 2 / condLB γ ^ Y.card := by positivity
  have : 2 ^ (n - S₁.card) * expect R (fun x ↦ |mu R u S₁ x - mu R u S x|) ≤
      2 ^ (n - S₁.card) * (2 / condLB γ ^ Y.card * expect R F) := by
    calc _ ≤ 2 / condLB γ ^ Y.card * (2 ^ (n - (Y ∪ S₁).card) * expect R F) := hmain
      _ ≤ 2 / condLB γ ^ Y.card * (2 ^ (n - S₁.card) * expect R F) := by gcongr
      _ = _ := by ring
  exact le_of_mul_le_mul_left this hpos

/-- Conditioning on one more variable `i` changes the proxy of a set `Y` with `N(u) ⊆ Y ∪ S` by at
most a factor `1 + 2 δ^{-|Y|}`. -/
theorem nu_le_nu_insert {γ : ℝ} (hW : R.WidthLE γ) {u i : Fin n} {S Y : Finset (Fin n)}
    (hi : i ∉ S) (hu : u ∉ Y ∪ insert i S) (hYS : Disjoint Y (insert i S))
    (hN : R.nbhd u ⊆ Y ∪ S) :
    R.nu u Y S ≤ (1 + 2 / condLB γ ^ Y.card) * R.nu u Y (insert i S) := by
  have hYS' : Disjoint Y S := hYS.mono_right (subset_insert i S)
  have hg : mu R u (Y ∪ insert i S) = mu R u (Y ∪ S) :=
    mu_eq_of_nbhd R (union_subset_union le_rfl (subset_insert i S)) hN hu
  rw [nu_eq R u hYS', nu_eq R u hYS, hg]
  have key := expect_abs_mu_insert_le R hW (u := u) hi hYS (mu R u (Y ∪ S)) (dep_mu R u (Y ∪ S))
  have tri : expect R (fun x ↦ |mu R u (Y ∪ S) x - mu R u S x|) ≤
      expect R (fun x ↦ |mu R u (Y ∪ S) x - mu R u (insert i S) x|) +
        expect R (fun x ↦ |mu R u (insert i S) x - mu R u S x|) := by
    rw [← expect_add]
    exact expect_mono R fun x ↦ abs_sub_le _ _ _
  calc expect R (fun x ↦ |mu R u (Y ∪ S) x - mu R u S x|) / 2 ^ (Y.card + 1)
      ≤ (1 + 2 / condLB γ ^ Y.card) *
          expect R (fun x ↦ |mu R u (Y ∪ S) x - mu R u (insert i S) x|) / 2 ^ (Y.card + 1) := by
        gcongr
        linarith
    _ = _ := by ring

/-- For a non-neighbour `i` of `u` and a nonempty `I` outside `S ∪ {u}`:
`ν_{u,I|S} ≤ 2^{D-1} · 3 δ^{-D} · ν_{u,N(u) ∖ S|S ∪ {i}}`. -/
theorem nu_le_of_notMem_nbhd {γ : ℝ} (hγ : 0 ≤ γ) (hW : R.WidthLE γ) {D : ℕ}
    (hDeg : R.DegreeLE D) {u i : Fin n} {S I : Finset (Fin n)} (hi : i ∉ S)
    (hiN : i ∉ R.nbhd u) (hu : u ∉ insert i S) (huI : u ∉ I) (hIS : Disjoint I S)
    (hI : I.Nonempty) :
    R.nu u I S ≤ 2 ^ D / 2 * (3 / condLB γ ^ D) * R.nu u (R.nbhd u \ S) (insert i S) := by
  set Y := R.nbhd u \ S with hY
  have huS : u ∉ S := fun h ↦ hu (mem_insert_of_mem h)
  have huY : u ∉ Y := fun h ↦ notMem_nbhd_self R u (mem_sdiff.1 h).1
  have hN : R.nbhd u ⊆ Y ∪ S := by
    intro j hj
    by_cases hjS : j ∈ S
    · exact mem_union_right _ hjS
    · exact mem_union_left _ (mem_sdiff.2 ⟨hj, hjS⟩)
  have hYS : Disjoint Y S := sdiff_disjoint
  have hYS₁ : Disjoint Y (insert i S) := by
    rw [disjoint_insert_right]
    exact ⟨fun h ↦ hiN (mem_sdiff.1 h).1, hYS⟩
  have h28 := nu_le_of_nbhd R (Z := I) (Y := Y) (S := S)
    (by simp only [mem_union, not_or]; exact ⟨huI, huS⟩)
    (by simp only [mem_union, not_or]; exact ⟨huY, huS⟩) hIS hYS hN
  have hcond := nu_le_nu_insert R hW hi
    (by simp only [mem_union, not_or]; exact ⟨huY, hu⟩) hYS₁ hN
  have hYcard : Y.card ≤ D := (card_le_card sdiff_subset).trans (hDeg u)
  have hIcard : 1 ≤ I.card := hI.card_pos
  have hδ0 := condLB_pos γ
  have hδ1 : condLB γ ≤ 1 := (condLB_le_half hγ).trans (by norm_num)
  have hν₁ := R.nu_nonneg u Y (insert i S)
  have hνY := R.nu_nonneg u Y S
  have hνI := R.nu_nonneg u I S
  -- `1 + 2 δ^{-|Y|} ≤ 3 δ^{-D}`
  have hfac : 1 + 2 / condLB γ ^ Y.card ≤ 3 / condLB γ ^ D := by
    have h1 : condLB γ ^ D ≤ condLB γ ^ Y.card := pow_le_pow_of_le_one hδ0.le hδ1 hYcard
    have h2 : condLB γ ^ Y.card ≤ 1 := pow_le_one₀ hδ0.le hδ1
    have h3 : 0 < condLB γ ^ D := pow_pos hδ0 D
    have h4 : 1 ≤ 1 / condLB γ ^ D := by rw [le_div_iff₀ h3]; linarith
    have h5 : 2 / condLB γ ^ Y.card ≤ 2 / condLB γ ^ D :=
      div_le_div_of_nonneg_left (by norm_num) h3 h1
    calc 1 + 2 / condLB γ ^ Y.card ≤ 1 / condLB γ ^ D + 2 / condLB γ ^ D := by linarith
      _ = 3 / condLB γ ^ D := by ring
  have hpowY : (2 : ℝ) ^ (Y.card + 1) ≤ 2 ^ (D + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hpowI : (2 : ℝ) ^ 2 ≤ 2 ^ (I.card + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hYS_le : R.nu u Y S ≤ 3 / condLB γ ^ D * R.nu u Y (insert i S) :=
    hcond.trans (mul_le_mul_of_nonneg_right hfac hν₁)
  have h4 : 4 * R.nu u I S ≤ 2 ^ (D + 1) * R.nu u Y S := by
    calc 4 * R.nu u I S = 2 ^ 2 * R.nu u I S := by norm_num
      _ ≤ 2 ^ (I.card + 1) * R.nu u I S := mul_le_mul_of_nonneg_right hpowI hνI
      _ ≤ 2 ^ (Y.card + 1) * R.nu u Y S := h28
      _ ≤ 2 ^ (D + 1) * R.nu u Y S := mul_le_mul_of_nonneg_right hpowY hνY
  have h5 : 2 ^ (D + 1) * R.nu u Y S ≤
      2 ^ (D + 1) * (3 / condLB γ ^ D * R.nu u Y (insert i S)) :=
    mul_le_mul_of_nonneg_left hYS_le (by positivity)
  rw [pow_succ] at h4 h5
  nlinarith

end BB20.Learning
