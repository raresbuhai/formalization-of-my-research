module

public import BB20.Structural.Latent
public import BB20.Structural.NonCancel

/-!
# Non-cancellation for one pattern

[BB20, Lemmas 15, 7 and 9]. The proxy `ν_{u,I|S}` (`BB20.RBM.nu`) is an average over configurations
`z` of `|T_I(z)|`, where `T_I(z) = P(z_u, z_I, z_S) - P(z_u, z_S) P(z_I, z_S) / P(z_S)`
(`BB20.Structural.nuTerm`).

* `BB20.Structural.nuTerm_eq`: for disjoint `{u}`, `I`, `S`,
  `T_I(z) = ∑_q c(q) ∏_{i ∈ I} pᵢ(zᵢ | q)` with
  `c(q) = π(q) ∏_{i ∈ S} pᵢ(zᵢ | q) · (p_u(z_u | q) - P(z_u, z_S) / P(z_S))`
  (`BB20.Structural.coef`), which does not depend on `I`.
* The product `∏_{i ∈ I'} pᵢ(zᵢ | q)` for `I' ⊆ I` depends only on the values of `q` on the set
  `U` of latent variables connected to `I` (`BB20.Structural.latSupp`). Grouping the `q` by these
  values (`BB20.Structural.restrictTo` sets the other values to `+1`) writes every `T_{I'}(z)`,
  `I' ⊆ I`, as `∑_r C(r) ∏_{i ∈ I'} pᵢ(zᵢ | r)` over at most `2^{|U|}` rows `r`, with the same
  coefficients `C`.
* `BB20.Structural.exists_subset_nuTerm` (Lemma 9): when `I ⊆ N(u)`, `|U| ≤ s`, and Lemma 8 gives
  `I' ⊆ I` with `|I'| ≤ 2^s` and `|T_I(z)| ≤ 4^{2^s} |I|^{2^s (2^s + 1)} |T_{I'}(z)|`.
-/

@[expose] public section

namespace BB20.Structural

open Finset

variable {n m : ℕ} (R : RBM n m)

/-- The term `T_I(z) = P(z_u, z_I, z_S) - P(z_u, z_S) P(z_I, z_S) / P(z_S)` of the configuration
`z` in `ν_{u,I|S}`, before taking absolute values. -/
noncomputable def nuTerm (u : Fin n) (I S : Finset (Fin n)) (z : Config n) : ℝ :=
  R.marg (insert u (I ∪ S)) z - R.marg (insert u S) z * R.marg (I ∪ S) z / R.marg S z

theorem nu_eq_sum_nuTerm (u : Fin n) (I S : Finset (Fin n)) :
    R.nu u I S = (∑ z, |nuTerm R u I S z|) / 2 ^ (n - S.card) := rfl

theorem nu_nonneg_of_nuTerm (u : Fin n) (I S : Finset (Fin n)) : 0 ≤ R.nu u I S := by
  rw [nu_eq_sum_nuTerm]
  exact div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by positivity)

theorem nuTerm_empty (u : Fin n) (S : Finset (Fin n)) (z : Config n) : nuTerm R u ∅ S z = 0 := by
  unfold nuTerm
  rw [empty_union, mul_div_assoc, div_self (marg_pos_latent R S z).ne', mul_one, sub_self]

/-- The coefficient `c(q) = π(q) ∏_{i ∈ S} pᵢ(zᵢ | q) · (p_u(z_u | q) - P(z_u, z_S) / P(z_S))`. -/
noncomputable def coef (u : Fin n) (S : Finset (Fin n)) (z : Config n) (q : Config m) : ℝ :=
  latProb R q * latCondSet R S z q *
    (latCond R u (z u) q - R.marg (insert u S) z / R.marg S z)

/-- `T_I(z) = ∑_q c(q) ∏_{i ∈ I} pᵢ(zᵢ | q)` for disjoint `{u}`, `I`, `S`. -/
theorem nuTerm_eq {u : Fin n} {I S : Finset (Fin n)} (huI : u ∉ I) (huS : u ∉ S)
    (hIS : Disjoint I S) (z : Config n) :
    nuTerm R u I S z = ∑ q, coef R u S z q * latCondSet R I z q := by
  have h1 : R.marg (insert u (I ∪ S)) z =
      ∑ q, latProb R q * latCondSet R S z q * latCond R u (z u) q * latCondSet R I z q := by
    rw [marg_eq_sum_latent]
    refine sum_congr rfl fun q _ ↦ ?_
    simp only [latCondSet]
    rw [prod_insert (by simp [huI, huS]), prod_union hIS]
    ring
  have h2 : R.marg (I ∪ S) z = ∑ q, latProb R q * latCondSet R S z q * latCondSet R I z q := by
    rw [marg_eq_sum_latent]
    refine sum_congr rfl fun q _ ↦ ?_
    simp only [latCondSet]
    rw [prod_union hIS]
    ring
  unfold nuTerm coef
  rw [h1, h2, mul_div_right_comm (R.marg (insert u S) z), mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun q _ ↦ ?_
  ring

open Classical in
/-- The latent variables connected to some observed variable in `I`. -/
noncomputable def latSupp (I : Finset (Fin n)) : Finset (Fin m) :=
  univ.filter fun j ↦ ∃ i ∈ I, R.J i j ≠ 0

/-- The latent configuration that agrees with `q` on `U` and is `+1` elsewhere. -/
def restrictTo (U : Finset (Fin m)) (q : Config m) : Config m :=
  fun j ↦ if j ∈ U then q j else true

theorem latField_restrictTo {i : Fin n} {U : Finset (Fin m)} (h : ∀ j ∉ U, R.J i j = 0)
    (q : Config m) : latField R i (restrictTo U q) = latField R i q := by
  unfold latField restrictTo
  congr 1
  refine sum_congr rfl fun j _ ↦ ?_
  by_cases hj : j ∈ U
  · simp [hj]
  · simp [hj, h j hj]

theorem latCondSet_restrictTo {I I' : Finset (Fin n)} (hI' : I' ⊆ I) (z : Config n)
    (q : Config m) : latCondSet R I' z (restrictTo (latSupp R I) q) = latCondSet R I' z q := by
  unfold latCondSet latCond
  refine prod_congr rfl fun i hi ↦ ?_
  rw [latField_restrictTo R]
  intro j hj
  by_contra hJ
  exact hj (by simpa [latSupp] using ⟨i, hI' hi, hJ⟩)

/-- Grouping a sum over latent configurations by their values on `U`. -/
theorem sum_regroup (U : Finset (Fin m)) (c P : Config m → ℝ)
    (hP : ∀ q, P (restrictTo U q) = P q) :
    ∑ q, c q * P q = ∑ r ∈ univ.image (restrictTo U),
      (∑ q ∈ univ.filter (fun q ↦ restrictTo U q = r), c q) * P r := by
  rw [← sum_fiberwise_of_maps_to (g := restrictTo U) (t := univ.image (restrictTo U))
    (fun q _ ↦ mem_image_of_mem _ (mem_univ q))]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [sum_mul]
  refine sum_congr rfl fun q hq ↦ ?_
  obtain ⟨-, rfl⟩ := mem_filter.mp hq
  rw [hP]

theorem card_image_restrictTo_le (U : Finset (Fin m)) :
    (univ.image (restrictTo U)).card ≤ 2 ^ U.card := by
  classical
  have hsub : univ.image (restrictTo U) ⊆
      univ.image (fun f : U → Bool ↦ fun j ↦ if h : j ∈ U then f ⟨j, h⟩ else true) := by
    intro r hr
    obtain ⟨q, -, rfl⟩ := mem_image.mp hr
    refine mem_image.mpr ⟨fun j ↦ q j, mem_univ _, ?_⟩
    funext j
    simp only [restrictTo]
    split_ifs <;> rfl
  calc _ ≤ _ := card_le_card hsub
    _ ≤ (univ : Finset (U → Bool)).card := card_image_le
    _ = 2 ^ U.card := by simp

/-- **[BB20, Lemma 9]**: for one configuration `z`, some `I' ⊆ I` with `|I'| ≤ 2^s` has
`|T_I(z)| ≤ 4^{2^s} |I|^{2^s (2^s + 1)} |T_{I'}(z)|`. -/
theorem exists_subset_nuTerm {s : ℕ} (hs : R.SparsityLE s) {u : Fin n} {I S : Finset (Fin n)}
    (hI : I ⊆ R.nbhd u) (hu : u ∉ S) (hIS : Disjoint I S) (hne : I.Nonempty) (z : Config n) :
    ∃ I' ⊆ I, I'.card ≤ 2 ^ s ∧
      |nuTerm R u I S z| ≤
        4 ^ 2 ^ s * (I.card : ℝ) ^ (2 ^ s * (2 ^ s + 1)) * |nuTerm R u I' S z| := by
  classical
  have huI : u ∉ I := fun h ↦ by simpa [RBM.nbhd] using hI h
  have hU : (latSupp R I).card ≤ s := by
    refine le_trans (card_le_card ?_) (hs u)
    intro j hj
    simp only [latSupp, mem_filter, mem_univ, true_and] at hj ⊢
    obtain ⟨i, hi, hJ⟩ := hj
    exact ⟨i, hI hi, hJ⟩
  have hrows : (univ.image (restrictTo (latSupp R I))).card ≤ 2 ^ s :=
    (card_image_restrictTo_le _).trans (Nat.pow_le_pow_right (by norm_num) hU)
  have hx : ∀ (r : Config m) (i : Fin n), |latCond R i (z i) r| ≤ 1 := fun r i ↦
    abs_latCond_le_one R _ _ _
  have hterm : ∀ I' ⊆ I, nuTerm R u I' S z = prodSum (univ.image (restrictTo (latSupp R I)))
      (fun r ↦ ∑ q ∈ univ.filter (fun q ↦ restrictTo (latSupp R I) q = r), coef R u S z q)
      (fun r i ↦ latCond R i (z i) r) I' := by
    intro I' hI'
    rw [nuTerm_eq R (fun h ↦ huI (hI' h)) hu (hIS.mono_left hI') z,
      sum_regroup _ _ _ (latCondSet_restrictTo R hI' z)]
    rfl
  obtain ⟨I', hI'I, hI'c, hb⟩ := exists_subset_noncancel _ hx (2 ^ s) _ hrows _ I hne
  refine ⟨I', hI'I, hI'c, ?_⟩
  rw [hterm I (subset_refl _), hterm I' hI'I]
  exact hb

end BB20.Structural
