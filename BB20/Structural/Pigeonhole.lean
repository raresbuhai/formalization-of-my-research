module

public import BB20.Structural.Pattern

/-!
# From one pattern to the proxy

[BB20, Lemma 10]. Lemma 9 (`BB20.Structural.exists_subset_nuTerm`) gives, for each configuration
`z`, a set `I*(z) ⊆ I` with `|I*(z)| ≤ 2^s` and `|T_I(z)| ≤ K |T_{I*(z)}(z)|`, with
`K = 4^{2^s} |I|^{2^s (2^s + 1)}`. Since `T_∅ = 0`, the sets that matter are the nonempty
`I' ⊆ I` with `|I'| ≤ 2^s`, and there are at most `|I|^{2^s}` of them
(`BB20.Structural.card_small_subsets_le`: each is the image of a map from `2^s` points to `I`).
Summing over `z`, `∑_z |T_I(z)| ≤ K ∑_{I'} ∑_z |T_{I'}(z)| ≤ K |I|^{2^s} max_{I'} ∑_z |T_{I'}(z)|`.
The proxies `ν_{u,I|S}` and `ν_{u,I'|S}` are these sums divided by the same number `2^{n - |S|}`,
so the maximizing `I'` satisfies `ν_{u,I|S} ≤ (4|I|)^{2^s} |I|^{2^s (2^s + 1)} ν_{u,I'|S}`
(`BB20.Structural.exists_subset_nu_ge`).
-/

@[expose] public section

namespace BB20.Structural

open Finset

variable {n m : ℕ}

/-- There are at most `|I|^M` nonempty subsets of `I` with at most `M` elements. -/
theorem card_small_subsets_le (I : Finset (Fin n)) (M : ℕ) :
    (I.powerset.filter fun I' ↦ I'.Nonempty ∧ I'.card ≤ M).card ≤ I.card ^ M := by
  classical
  have hsub : (I.powerset.filter fun I' ↦ I'.Nonempty ∧ I'.card ≤ M) ⊆
      (Fintype.piFinset fun _ : Fin M ↦ I).image (fun f ↦ univ.image f) := by
    intro I' hI'
    simp only [mem_filter, mem_powerset] at hI'
    obtain ⟨hI'I, hne, hc⟩ := hI'
    have hk : 0 < I'.card := card_pos.mpr hne
    let e := I'.orderEmbOfFin rfl
    refine mem_image.mpr ⟨fun t ↦ e ⟨min t.1 (I'.card - 1), by omega⟩, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      exact fun t ↦ hI'I (I'.orderEmbOfFin_mem rfl _)
    · ext y
      simp only [mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨t, rfl⟩
        exact I'.orderEmbOfFin_mem rfl _
      · intro hy
        have : y ∈ Set.range e := by
          rw [Finset.range_orderEmbOfFin]
          exact hy
        obtain ⟨t, rfl⟩ := this
        refine ⟨⟨t.1, by omega⟩, ?_⟩
        congr 1
        ext
        simp only
        omega
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_image_le
    _ = I.card ^ M := by simp

variable (R : RBM n m)

/-- **[BB20, Lemma 10]**, which is Theorem 4: some `I' ⊆ I` with `|I'| ≤ 2^s` has
`ν_{u,I|S} / ((4|I|)^{2^s} |I|^{2^s (2^s + 1)}) ≤ ν_{u,I'|S}`. -/
theorem exists_subset_nu_ge (s : ℕ) (hs : R.SparsityLE s) (u : Fin n)
    (I S : Finset (Fin n)) (hI : I ⊆ R.nbhd u) (hu : u ∉ S) (hIS : Disjoint I S) :
    ∃ I' ⊆ I, I'.card ≤ 2 ^ s ∧
      R.nu u I S / ((4 * I.card : ℝ) ^ 2 ^ s * (I.card : ℝ) ^ (2 ^ s * (2 ^ s + 1))) ≤
        R.nu u I' S := by
  classical
  rcases I.eq_empty_or_nonempty with rfl | hne
  · refine ⟨∅, subset_refl _, by simp, ?_⟩
    simp only [card_empty, Nat.cast_zero, mul_zero]
    rw [zero_pow (by positivity), zero_mul, div_zero]
    exact nu_nonneg_of_nuTerm R u ∅ S
  have hN : (1 : ℝ) ≤ I.card := by exact_mod_cast card_pos.mpr hne
  choose J hJI hJc hJ using fun z ↦ exists_subset_nuTerm R hs hI hu hIS hne z
  set M := 2 ^ s with hM
  set C := I.powerset.filter fun I' ↦ I'.Nonempty ∧ I'.card ≤ M with hC
  set G : Finset (Fin n) → ℝ := fun I' ↦ ∑ z, |nuTerm R u I' S z| with hG
  have hCne : C.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    refine ⟨{i}, ?_⟩
    simp only [hC, mem_filter, mem_powerset, singleton_subset_iff, singleton_nonempty,
      card_singleton, true_and]
    exact ⟨hi, Nat.one_le_two_pow⟩
  obtain ⟨I₀, hI₀, hmax⟩ := exists_max_image C G hCne
  set K : ℝ := 4 ^ M * (I.card : ℝ) ^ (M * (M + 1)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hz : ∀ z, |nuTerm R u I S z| ≤ K * ∑ I' ∈ C, |nuTerm R u I' S z| := by
    intro z
    refine (hJ z).trans (mul_le_mul_of_nonneg_left ?_ hK0)
    rcases (J z).eq_empty_or_nonempty with h | h
    · rw [h, nuTerm_empty, abs_zero]
      exact sum_nonneg fun _ _ ↦ abs_nonneg _
    · refine single_le_sum (f := fun I' ↦ |nuTerm R u I' S z|) (fun _ _ ↦ abs_nonneg _) ?_
      simp only [hC, mem_filter, mem_powerset]
      exact ⟨hJI z, h, hJc z⟩
  have hG0 : 0 ≤ G I₀ := sum_nonneg fun _ _ ↦ abs_nonneg _
  have hsum : G I ≤ K * (I.card : ℝ) ^ M * G I₀ := by
    calc G I ≤ ∑ z, K * ∑ I' ∈ C, |nuTerm R u I' S z| := sum_le_sum fun z _ ↦ hz z
      _ = K * ∑ I' ∈ C, G I' := by rw [← mul_sum, sum_comm]
      _ ≤ K * (C.card * G I₀) := by
        gcongr
        calc ∑ I' ∈ C, G I' ≤ ∑ _I' ∈ C, G I₀ := sum_le_sum fun I' h ↦ hmax I' h
          _ = C.card * G I₀ := by rw [sum_const, nsmul_eq_mul]
      _ ≤ K * ((I.card : ℝ) ^ M * G I₀) := by
        gcongr
        exact_mod_cast card_small_subsets_le I M
      _ = _ := by ring
  have hI₀' := mem_filter.mp hI₀
  refine ⟨I₀, mem_powerset.mp hI₀'.1, hI₀'.2.2, ?_⟩
  rw [nu_eq_sum_nuTerm, nu_eq_sum_nuTerm]
  have hden : (4 * (I.card : ℝ)) ^ M * (I.card : ℝ) ^ (M * (M + 1)) = K * (I.card : ℝ) ^ M := by
    rw [hK, mul_pow]
    ring
  have hpos : (0 : ℝ) < K * (I.card : ℝ) ^ M := by positivity
  have h2 : (0 : ℝ) < 2 ^ (n - S.card) := by positivity
  rw [hden, div_le_iff₀ hpos, div_mul_eq_mul_div, div_le_div_iff_of_pos_right h2]
  linarith

end BB20.Structural
