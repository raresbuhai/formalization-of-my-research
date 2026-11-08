module

public import BB20.Learning.Algorithm
public import BB20.Learning.Concentration
public import BB20.Learning.Greedy
public import BB20.Learning.Prune
public import BB20.Learning.Bounds

/-!
# Correctness of the structure-learning algorithms

For every threshold function meeting its specification, the algorithm of Theorem 6 recovers all
MRF neighbourhoods, and that of Theorem 11 recovers all `ζ`-strong neighbours and only neighbours,
with probability at least `1 - ω` at the sample sizes of the theorems.

The proofs are in `BB20/Learning/`:

* the good event (`BB20/Learning/Concentration.lean`): all empirical marginals on at most
  `⌊L⌋ + 2^s + 1` variables are within `σ = τ'/(8 · 2^L)` of the true ones; it has probability at
  least `1 - ω` at the sample size (`BB20.Learning.sample_bound`), and on it the empirical proxy
  is within `τ'/2` of `ν` on the sets the algorithm looks at;
* the greedy phase (`BB20/Learning/Greedy.lean`), bounded through the potential
  `Ψ(S) = E[m_S²]` (`BB20/Learning/Progress.lean`);
* the pruning steps: here for Theorem 6 (`BB20.Learning.prune6`), and with Lemma 28 and
  conditioning on one more variable (`BB20/Learning/Prune.lean`) for Theorem 11
  (`BB20.Learning.prune11`).
-/

@[expose] public section

namespace BB20.Learning

open Finset

/-! ### The sample size -/

/-- At the sample size, `M ≥ 1` and `2 M σ² ≥ log 2 + log K + K log(2n) + log(1/ω)` with
`σ = τ'/(8 · 2^L)` and `K = ⌊L⌋ + 2^s + 1`. -/
theorem sample_bound {α γ : ℝ} {d D s n : ℕ} {ω : ℝ} {M : ℕ} (hτ : 0 < tauPrime α γ d D s)
    (hγ : 0 ≤ γ) (hn : 1 ≤ n) (hω : 0 < ω) (hω1 : ω ≤ 1) (hM : sampleSize α γ d D s n ω ≤ M) :
    1 ≤ M ∧ Real.log 2 + Real.log ((⌊stepBound α γ d D s⌋₊ + 2 ^ s + 1 : ℕ) : ℝ) +
      ((⌊stepBound α γ d D s⌋₊ + 2 ^ s + 1 : ℕ) : ℝ) * Real.log (2 * n) + Real.log (1 / ω) ≤
      2 * M * (tauPrime α γ d D s / (8 * (2 : ℝ) ^ stepBound α γ d D s)) ^ 2 := by
  set τ := tauPrime α γ d D s with hτdef
  set L := stepBound α γ d D s with hLdef
  have hL : L = 2 ^ s * 8 / τ ^ 2 := rfl
  have hL0 : 0 < L := by rw [hL]; positivity
  have hδ := condLB_pos γ
  have hδ1 : condLB γ ≤ 1 := (condLB_le_half hγ).trans (by norm_num)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2n : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
  have hlogω : 0 ≤ Real.log (1 / ω) := Real.log_nonneg (by rw [le_div_iff₀ hω]; linarith)
  have hs1 : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  have hlogL : 0 ≤ Real.log (L + 2 ^ s + 1) := Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Lg, hLg⟩ : ∃ Lg, Lg = Real.log (1 / ω) + Real.log (L + 2 ^ s + 1) +
      (L + 2 ^ s + 1) * Real.log (2 * n) + Real.log 2 := ⟨_, rfl⟩
  have hLgpos : 0 < Lg := by
    have : 0 ≤ (L + 2 ^ s + 1) * Real.log (2 * n) := mul_nonneg (by linarith) hlog2n
    linarith
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = 60 * (2 : ℝ) ^ (2 * L) / (τ ^ 2 * condLB γ ^ (2 * L)) :=
    ⟨_, rfl⟩
  have hss : sampleSize α γ d D s n ω = C₀ * Lg := by rw [hC₀, hLg]; rfl
  have h2L : (2 : ℝ) ^ (2 * L) = ((2 : ℝ) ^ L) ^ 2 := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_two]
  have hδL : condLB γ ^ (2 * L) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have hδL0 : 0 < condLB γ ^ (2 * L) := Real.rpow_pos_of_pos hδ _
  have h2Lpos : 0 < (2 : ℝ) ^ L := Real.rpow_pos_of_pos (by norm_num) _
  have hC₀pos : 0 < C₀ := by rw [hC₀]; positivity
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (mul_pos hC₀pos hLgpos) (hss ▸ hM)
  refine ⟨by exact_mod_cast hMpos, ?_⟩
  have hK' : (((⌊L⌋₊ + 2 ^ s + 1 : ℕ) : ℝ)) ≤ L + 2 ^ s + 1 := by
    push_cast
    have := Nat.floor_le hL0.le
    linarith
  have hK1 : (1 : ℝ) ≤ ((⌊L⌋₊ + 2 ^ s + 1 : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ ⌊L⌋₊ := Nat.cast_nonneg _
    linarith
  have hlogK : Real.log ((⌊L⌋₊ + 2 ^ s + 1 : ℕ) : ℝ) ≤ Real.log (L + 2 ^ s + 1) :=
    Real.log_le_log (by linarith) hK'
  have hstep1 : Real.log 2 + Real.log ((⌊L⌋₊ + 2 ^ s + 1 : ℕ) : ℝ) +
      ((⌊L⌋₊ + 2 ^ s + 1 : ℕ) : ℝ) * Real.log (2 * n) + Real.log (1 / ω) ≤ Lg := by
    have := mul_le_mul_of_nonneg_right hK' hlog2n
    rw [hLg]
    linarith
  have hσC : 1 ≤ 2 * (τ / (8 * 2 ^ L)) ^ 2 * C₀ := by
    rw [hC₀, h2L]
    rw [show 2 * (τ / (8 * 2 ^ L)) ^ 2 * (60 * ((2 : ℝ) ^ L) ^ 2 /
        (τ ^ 2 * condLB γ ^ (2 * L))) = 120 / (64 * condLB γ ^ (2 * L)) by field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc _ ≤ Lg := hstep1
    _ ≤ 2 * (τ / (8 * 2 ^ L)) ^ 2 * C₀ * Lg := le_mul_of_one_le_left hLgpos.le hσC
    _ = 2 * (τ / (8 * 2 ^ L)) ^ 2 * (C₀ * Lg) := by ring
    _ ≤ 2 * (τ / (8 * 2 ^ L)) ^ 2 * M := by
        gcongr
        rw [← hss]
        exact hM
    _ = 2 * M * (τ / (8 * 2 ^ L)) ^ 2 := by ring

/-- **From the good event to the probability bound**: at the sample size, with probability at
least `1 - ω` the algorithm's empirical proxy is within `τ'/2` of `ν`, at every variable, on the
sets of at most `2^s` variables given sets of at most `L` variables. -/
theorem prob_of_accurate {n m : ℕ} (R : RBM n m) {α γ : ℝ} {d D s : ℕ} {ω : ℝ} {M : ℕ}
    (hτ : 0 < tauPrime α γ d D s) (hγ : 0 ≤ γ) (hn : 1 ≤ n) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hM : sampleSize α γ d D s n ω ≤ M) (P : (Fin M → Config n) → Prop)
    (hdet : ∀ X : Fin M → Config n, 1 ≤ M →
      (∀ u : Fin n, Accurate R u (fun I S ↦ empNuL (sampleList X) n u I S) (2 ^ s)
        (stepBound α γ d D s) (tauPrime α γ d D s / 2)) → P X) :
    1 - ω ≤ R.sampleProb M P := by
  obtain ⟨hM1, hMσ⟩ := sample_bound hτ hγ hn hω hω1 hM
  set L := stepBound α γ d D s
  set σ := tauPrime α γ d D s / (8 * (2 : ℝ) ^ L) with hσdef
  have h2L : 0 < (2 : ℝ) ^ L := Real.rpow_pos_of_pos (by norm_num) _
  have hσ : 0 < σ := by positivity
  have hK1 : 1 ≤ ⌊L⌋₊ + 2 ^ s + 1 := Nat.le_add_left 1 _
  refine (good_prob R hM1 hn hσ hK1 hω hMσ).trans
    (sampleProb_mono R M fun X hX ↦ hdet X hM1 fun u ↦ ?_)
  have := accurate_of_good R X u s _ hσ.le le_rfl hX
  have e : 4 * (2 : ℝ) ^ L * σ = tauPrime α γ d D s / 2 := by
    rw [hσdef]
    field_simp
    ring
  rwa [e] at this

/-! ### Sets of variables as numbers -/

theorem map_val_erase {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    (S.map Fin.valEmbedding).erase (i : ℕ) = (S.erase i).map Fin.valEmbedding := by
  rw [map_erase]
  rfl

theorem map_val_singleton {n : ℕ} (i : Fin n) :
    ({(i : ℕ)} : Finset ℕ) = ({i} : Finset (Fin n)).map Fin.valEmbedding := by
  rw [map_singleton]
  rfl

theorem not_subset_insert {n : ℕ} {u i : Fin n} {S T : Finset (Fin n)} (hiu : i ≠ u)
    (hiS : i ∉ S) (hiT : i ∈ T) : ¬ T ⊆ insert u S := fun h ↦ by
  rcases mem_insert.1 (h hiT) with h | h
  · exact hiu h
  · exact hiS h

variable {n m : ℕ}

/-! ### The pruning step of Theorem 6 -/

/-- **The algorithm of Theorem 6 at one variable**: on accurate empirical proxies, the pruned
greedy set is `N(u)`. -/
theorem prune6 (R : RBM n m) {α γ : ℝ} {d D s : ℕ} (hα : 0 < α) (hγ : 0 < γ) (hd : 1 ≤ d)
    (hmin : R.MinCoeffGE α) (hW : R.WidthLE γ) (hL : R.LatentDegreeLE d)
    (hDeg : R.DegreeLE D) (hs : R.SparsityLE s) (u : Fin n) (nh : Finset ℕ → Finset ℕ → ℚ)
    (t : ℚ) (ht1 : 9 / 10 * tauPrime α γ d D s ≤ t) (ht2 : (t : ℝ) ≤ tauPrime α γ d D s)
    (hacc : Accurate R u nh (2 ^ s) (stepBound α γ d D s) (tauPrime α γ d D s / 2)) :
    (greedy nh n u (2 ^ s) t).filter (fun i ↦ t < nh {i} ((greedy nh n u (2 ^ s) t).erase i)) =
      (R.nbhd u).map Fin.valEmbedding := by
  set τ := tauPrime α γ d D s with hτdef
  have hτ : 0 < τ := tauPrime_pos hα.ne' hγ hd
  obtain ⟨S, hSmap, huS, hSL, hfix⟩ := greedy_spec R u nh s t hτ ht1 ht2 hacc
  rw [← hSmap]
  have hnb : ∀ i ∈ R.nbhd u, i ≠ u ∧ ∃ T, u ∈ T ∧ i ∈ T ∧ R.fourier T ≠ 0 := by
    intro i hi
    simpa [RBM.nbhd] using hi
  have hcoef : ∀ i T, i ≠ u → u ∈ T → i ∈ T → R.fourier T ≠ 0 → α ≤ |R.fourier T| :=
    fun i T hiu huT hiT hT ↦ hmin T (one_lt_card.2 ⟨u, huT, i, hiT, hiu.symm⟩) hT
  -- the greedy set contains `N(u)`
  have hN : R.nbhd u ⊆ S := by
    intro i hi
    by_contra hiS
    obtain ⟨hiu, T, huT, hiT, hT⟩ := hnb i hi
    obtain ⟨I, hI, -, hcard, hν⟩ := exists_cand R hγ hd hW hL hDeg hs huS hα huT
      (not_subset_insert hiu hiS hiT) (hcoef i T hiu huT hiT hT)
    have huI : u ∉ I := fun h ↦ notMem_nbhd_self R u (mem_sdiff.1 (hI h)).1
    have := hfix I huI (disjoint_of_subset_left hI sdiff_disjoint) hcard
    linarith
  have hacc1 : ∀ i ∈ S, |(nh {(i : ℕ)} ((S.map Fin.valEmbedding).erase i) : ℝ) -
      R.nu u {i} (S.erase i)| ≤ τ / 2 := by
    intro i hiS
    have hiu : i ≠ u := fun h ↦ huS (h ▸ hiS)
    rw [map_val_erase, map_val_singleton]
    refine hacc {i} (S.erase i) (by simpa using hiu.symm) (fun h ↦ huS (mem_of_mem_erase h))
      (disjoint_singleton_left.2 (notMem_erase i S)) (by simp [Nat.one_le_two_pow]) ?_
    exact le_trans (by exact_mod_cast card_erase_le) hSL
  ext a
  simp only [mem_filter, mem_map, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨⟨i, hiS, rfl⟩, ht⟩
    refine ⟨i, ?_, rfl⟩
    by_contra hiN
    have hiu : i ≠ u := fun h ↦ huS (h ▸ hiS)
    have hN' : R.nbhd u ⊆ S.erase i := fun j hj ↦
      mem_erase.2 ⟨fun h ↦ hiN (h ▸ hj), hN hj⟩
    have hν0 := R.nu_eq_zero_of_nbhd_subset u {i} (S.erase i)
      (by
        simp only [mem_union, mem_singleton, not_or]
        exact ⟨hiu.symm, fun h ↦ huS (mem_of_mem_erase h)⟩) hN'
    have h1 := (abs_le.1 (hacc1 i hiS)).2
    rw [hν0] at h1
    have h2 : (t : ℝ) < nh {(i : ℕ)} ((S.map Fin.valEmbedding).erase i) := by exact_mod_cast ht
    linarith
  · rintro ⟨i, hiN, rfl⟩
    have hiS := hN hiN
    refine ⟨⟨i, hiS, rfl⟩, ?_⟩
    obtain ⟨hiu, T, huT, hiT, hT⟩ := hnb i hiN
    have huS' : u ∉ S.erase i := fun h ↦ huS (mem_of_mem_erase h)
    obtain ⟨I, hI, hne, -, hν⟩ := exists_cand R hγ hd hW hL hDeg hs huS' hα huT
      (not_subset_insert hiu (notMem_erase i S) hiT) (hcoef i T hiu huT hiT hT)
    have hIi : I = {i} := by
      refine (hne.subset_singleton_iff).1 fun j hj ↦ ?_
      obtain ⟨hjN, hjS⟩ := mem_sdiff.1 (hI hj)
      rw [mem_singleton]
      by_contra hji
      exact hjS (mem_erase.2 ⟨hji, hN hjN⟩)
    rw [hIi] at hν
    have h1 := (abs_le.1 (hacc1 i hiS)).1
    exact_mod_cast (show (t : ℝ) < nh {(i : ℕ)} ((S.map Fin.valEmbedding).erase i) by linarith)

/-! ### The pruning step of Theorem 11 -/

/-- **The algorithm of Theorem 11 at one variable**: on accurate empirical proxies, the pruned
greedy set contains every `ζ`-strong neighbour of `u` and only neighbours of `u`. -/
theorem prune11 (R : RBM n m) {ζ γ : ℝ} {d D s : ℕ} (hζ : 0 < ζ) (hγ : 0 < γ) (hd : 1 ≤ d)
    (hD : 1 ≤ D) (hW : R.WidthLE γ) (hL : R.LatentDegreeLE d) (hDeg : R.DegreeLE D)
    (hs : R.SparsityLE s) (u : Fin n) (nh : Finset ℕ → Finset ℕ → ℚ) (t₂ t₃ : ℚ)
    (ht₂1 : 9 / 10 * tauPrime (ζ * eta γ D s) γ d D s ≤ t₂)
    (ht₂2 : (t₂ : ℝ) ≤ tauPrime (ζ * eta γ D s) γ d D s)
    (ht₃1 : 9 / 10 * tauPrime ζ γ d D s ≤ t₃) (ht₃2 : (t₃ : ℝ) ≤ tauPrime ζ γ d D s)
    (hacc : Accurate R u nh (2 ^ s) (stepBound (ζ * eta γ D s) γ d D s)
      (tauPrime (ζ * eta γ D s) γ d D s / 2)) :
    (R.strongNbhd ζ u).map Fin.valEmbedding ⊆
        (greedy nh n u (2 ^ s) t₂).filter (fun i ↦ (candList n u (2 ^ s)
          ((greedy nh n u (2 ^ s) t₂).erase i)).any fun l ↦
            decide (t₃ < nh l.toFinset ((greedy nh n u (2 ^ s) t₂).erase i))) ∧
      (greedy nh n u (2 ^ s) t₂).filter (fun i ↦ (candList n u (2 ^ s)
          ((greedy nh n u (2 ^ s) t₂).erase i)).any fun l ↦
            decide (t₃ < nh l.toFinset ((greedy nh n u (2 ^ s) t₂).erase i))) ⊆
        (R.nbhd u).map Fin.valEmbedding := by
  set η := eta γ D s with hηdef
  set τ₂ := tauPrime (ζ * η) γ d D s with hτ₂def
  set τ₃ := tauPrime ζ γ d D s with hτ₃def
  have hη := eta_pos γ hD s
  have hτ₃ : 0 < τ₃ := tauPrime_pos hζ.ne' hγ hd
  have hτ₂ : 0 < τ₂ := tauPrime_pos (mul_pos hζ hη).ne' hγ hd
  have hτ₂₃ : τ₂ = η ^ 2 * τ₃ := tauPrime_mul ζ η γ d D s
  have hη2 : η ^ 2 ≤ 1 / 6 := eta_sq_le hγ.le hD s
  obtain ⟨S, hSmap, huS, hSL, hfix⟩ := greedy_spec R u nh s t₂ hτ₂ ht₂1 ht₂2 hacc
  rw [← hSmap]
  have hstr : ∀ i ∈ R.strongNbhd ζ u, i ≠ u ∧ ∃ T, u ∈ T ∧ i ∈ T ∧ ζ ≤ |R.fourier T| := by
    intro i hi
    simpa [RBM.strongNbhd] using hi
  have hSerase : ∀ i, ((S.erase i).card : ℝ) ≤ stepBound (ζ * η) γ d D s := fun i ↦
    le_trans (by exact_mod_cast card_erase_le) hSL
  -- the greedy set contains the `ζ`-strong neighbours
  have hstrong : R.strongNbhd ζ u ⊆ S := by
    intro i hi
    by_contra hiS
    obtain ⟨hiu, T, huT, hiT, hT⟩ := hstr i hi
    have hηζ : ζ * η ≤ |R.fourier T| :=
      le_trans (mul_le_of_le_one_right hζ.le (eta_le_one hγ.le hD s)) hT
    obtain ⟨I, hI, -, hcard, hν⟩ := exists_cand R hγ hd hW hL hDeg hs huS (mul_pos hζ hη) huT
      (not_subset_insert hiu hiS hiT) hηζ
    have huI : u ∉ I := fun h ↦ notMem_nbhd_self R u (mem_sdiff.1 (hI h)).1
    have := hfix I huI (disjoint_of_subset_left hI sdiff_disjoint) hcard
    linarith
  constructor
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_map.1 ha
    have hiS := hstrong hi
    rw [mem_filter]
    refine ⟨mem_map_of_mem _ hiS, ?_⟩
    rw [List.any_eq_true]
    obtain ⟨hiu, T, huT, hiT, hT⟩ := hstr i hi
    have huS' : u ∉ S.erase i := fun h ↦ huS (mem_of_mem_erase h)
    obtain ⟨I, hI, hne, hcard, hν⟩ := exists_cand R hγ hd hW hL hDeg hs huS' hζ huT
      (not_subset_insert hiu (notMem_erase i S) hiT) hT
    have huI : u ∉ I := fun h ↦ notMem_nbhd_self R u (mem_sdiff.1 (hI h)).1
    have hdisj : Disjoint I (S.erase i) := disjoint_of_subset_left hI sdiff_disjoint
    refine ⟨(I.map Fin.valEmbedding).sort (· ≤ ·), ?_, ?_⟩
    · rw [Fin.valEmbedding_apply, map_val_erase]
      refine sort_mem_candList hne.map (by rw [card_map]; exact hcard) fun j hj ↦ ?_
      obtain ⟨b, hb, rfl⟩ := mem_map.1 hj
      refine ⟨b.2, fun h ↦ huI (Fin.ext h ▸ hb), fun h ↦ ?_⟩
      obtain ⟨c, hc, hcb⟩ := mem_map.1 h
      have : c = b := Fin.ext hcb
      exact disjoint_left.1 hdisj hb (this ▸ hc)
    · rw [sort_toFinset, decide_eq_true_eq, Fin.valEmbedding_apply, map_val_erase]
      have h1 := (abs_le.1 (hacc I (S.erase i) huI huS' hdisj hcard (hSerase i))).1
      have h2 : τ₂ ≤ τ₃ := by rw [hτ₂₃]; nlinarith
      exact_mod_cast (show (t₃ : ℝ) < nh (I.map Fin.valEmbedding)
        ((S.erase i).map Fin.valEmbedding) by linarith)
  · intro a ha
    obtain ⟨haS, hany⟩ := mem_filter.1 ha
    obtain ⟨i, hiS, rfl⟩ := mem_map.1 haS
    refine mem_map_of_mem _ ?_
    by_contra hiN
    rw [List.any_eq_true, Fin.valEmbedding_apply, map_val_erase] at hany
    obtain ⟨l, hl, hlt⟩ := hany
    rw [decide_eq_true_eq] at hlt
    obtain ⟨hlne, hlk, hlp⟩ := cand_props hl
    set S'' := S.erase i with hS''def
    set I := toFin n l.toFinset with hIdef
    have hlI : I.map Fin.valEmbedding = l.toFinset := map_toFin fun b hb ↦ (hlp b hb).1
    have huI : u ∉ I := fun h ↦ (hlp u (mem_toFin.1 h)).2.1 rfl
    have hdisj : Disjoint I S'' := by
      rw [disjoint_left]
      intro b hb hbS
      exact (hlp b (mem_toFin.1 hb)).2.2 (mem_map_of_mem _ hbS)
    have hcardI : I.card ≤ 2 ^ s := by
      rw [← card_map Fin.valEmbedding, hlI]
      exact hlk
    have hIne : I.Nonempty := by
      rw [← map_nonempty (f := Fin.valEmbedding), hlI]
      exact hlne
    have huS'' : u ∉ S'' := fun h ↦ huS (mem_of_mem_erase h)
    have hins : insert i S'' = S := insert_erase hiS
    have hchain := nu_le_of_notMem_nbhd R hγ.le hW hDeg (notMem_erase i S) hiN
      (by rw [hins]; exact huS) huI hdisj hIne
    rw [hins] at hchain
    -- the proxy of `Y = N(u) ∖ S''` given `S`
    set Y := R.nbhd u \ S'' with hYdef
    have hYS : Disjoint Y S := by
      rw [disjoint_left]
      intro j hjY hjS
      obtain ⟨hjN, hjS''⟩ := mem_sdiff.1 hjY
      by_cases hji : j = i
      · exact hiN (hji ▸ hjN)
      · exact hjS'' (mem_erase.2 ⟨hji, hjS⟩)
    have hY : R.nu u Y S ≤ thmFactor s D * (3 / 2 * τ₂) := by
      obtain ⟨I', hI'Y, hcard', hν'⟩ :=
        Structural.nuSubsetBound R s hs u Y S sdiff_subset huS hYS
      have huI' : u ∉ I' := fun h ↦ notMem_nbhd_self R u (mem_sdiff.1 (hI'Y h)).1
      have hfix' := hfix I' huI' (disjoint_of_subset_left hI'Y hYS) hcard'
      rcases Y.eq_empty_or_nonempty with hY0 | hYne
      · rw [hY0, nu_empty]
        have : (1 : ℝ) ≤ thmFactor s D := one_le_thmFactor s (by exact_mod_cast hD)
        positivity
      · have hc1 : (1 : ℝ) ≤ Y.card := by exact_mod_cast hYne.card_pos
        have hcD : (Y.card : ℝ) ≤ D := by
          exact_mod_cast (card_le_card sdiff_subset).trans (hDeg u)
        have hFpos : 0 < thmFactor s Y.card := lt_of_lt_of_le one_pos (one_le_thmFactor s hc1)
        have hF : thmFactor s Y.card ≤ thmFactor s D := thmFactor_mono s (by linarith) hcD
        have h1 : R.nu u Y S / thmFactor s Y.card ≤ 3 / 2 * τ₂ := hν'.trans hfix'
        rw [div_le_iff₀ hFpos] at h1
        calc R.nu u Y S ≤ 3 / 2 * τ₂ * thmFactor s Y.card := h1
          _ ≤ 3 / 2 * τ₂ * thmFactor s D := by gcongr
          _ = thmFactor s D * (3 / 2 * τ₂) := by ring
    have hδ := condLB_pos γ
    have hfinal : R.nu u I S'' ≤ 3 / 8 * τ₃ := by
      have key := thmFactor_mul_eta_sq γ hD s
      calc R.nu u I S'' ≤ 2 ^ D / 2 * (3 / condLB γ ^ D) * R.nu u Y S := hchain
        _ ≤ 2 ^ D / 2 * (3 / condLB γ ^ D) * (thmFactor s D * (3 / 2 * τ₂)) := by gcongr
        _ = 2 ^ D / 2 * (3 / condLB γ ^ D) * (3 / 2) * (thmFactor s D * η ^ 2) * τ₃ := by
            rw [hτ₂₃]
            ring
        _ = 3 / 8 * τ₃ := by
            rw [key]
            field_simp
            ring
    have h1 := (abs_le.1 (hacc I S'' huI huS'' hdisj hcardI (hSerase i))).2
    rw [hlI] at h1
    have h2 : (t₃ : ℝ) < nh l.toFinset (S''.map Fin.valEmbedding) := by exact_mod_cast hlt
    have h3 : τ₂ ≤ τ₃ / 6 := by rw [hτ₂₃]; nlinarith
    linarith

/-! ### The theorems -/

theorem sampleProb_true (R : RBM n m) (M : ℕ) : R.sampleProb M (fun _ ↦ True) = 1 := by
  rw [sampleProb_eq_one_sub]
  simp [RBM.sampleProb]

theorem wellFormed_sampleList {M : ℕ} (hM : 1 ≤ M) (X : Fin M → Config n) (a : ℚ) (g : ℚ)
    (d D s : ℕ) : WellFormed ⟨n, sampleList X, a, g, d, D, s⟩ := by
  refine ⟨?_, fun l hl ↦ ?_⟩
  · intro h
    have := congrArg List.length h
    rw [length_sampleList] at this
    simp at this
    omega
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hl
    simp

/-- **Correctness of the algorithm of Theorem 6.** -/
theorem alg6_correct (thr : Input → Option ℚ) (hthr : ThrSpec6 thr) (n m : ℕ) (R : RBM n m)
    (α γ : ℚ) (d D s : ℕ) (hα : 0 < α) (hγ : 0 < γ) (hd : 1 ≤ d) (hmin : R.MinCoeffGE α)
    (hW : R.WidthLE γ) (hL : R.LatentDegreeLE d) (hDeg : R.DegreeLE D) (hs : R.SparsityLE s)
    (ω : ℝ) (M : ℕ) (hω : 0 < ω) (hM : sampleSize α γ d D s n ω ≤ M) :
    1 - ω ≤ R.sampleProb M fun X ↦ R.Recovers (alg6 thr ⟨n, sampleList X, α, γ, d, D, s⟩) := by
  by_cases hω1 : 1 < ω
  · exact (by linarith : 1 - ω ≤ 0).trans (sampleProb_nonneg R M _)
  push Not at hω1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine le_trans ?_ (sampleProb_mono R M (Q := fun _ ↦ True) fun X _ u ↦ u.elim0)
    rw [sampleProb_true]
    linarith
  have hα' : (0 : ℝ) < α := by exact_mod_cast hα
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hτ := tauPrime_pos (D := D) (s := s) hα'.ne' hγ' hd
  refine prob_of_accurate R hτ hγ'.le hn hω hω1 hM _ fun X hM1 hacc ↦ ?_
  obtain ⟨t, hthr_eq, ht1, ht2⟩ := hthr n (sampleList X) α γ d D s ω hn hα hγ hd hω hω1
    (by rw [length_sampleList]; exact hM)
  intro u
  have hwf := wellFormed_sampleList hM1 X α γ d D s
  have hout := prune6 R hα' hγ' hd hmin hW hL hDeg hs u _ t ht1 ht2 (hacc u)
  rw [← hout]
  simp only [alg6, ite_eq_left hwf, hthr_eq, outNbhd]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range u.2]
  simp

/-- **Correctness of the algorithm of Theorem 11.** -/
theorem alg11_correct (thr : Input → Option (ℚ × ℚ)) (hthr : ThrSpec11 thr) (n m : ℕ)
    (R : RBM n m) (ζ γ : ℚ) (d D s : ℕ) (hζ : 0 < ζ) (hγ : 0 < γ) (hd : 1 ≤ d) (hD : 1 ≤ D)
    (hW : R.WidthLE γ) (hL : R.LatentDegreeLE d) (hDeg : R.DegreeLE D) (hs : R.SparsityLE s)
    (ω : ℝ) (M : ℕ) (hω : 0 < ω) (hM : sampleSize (ζ * eta γ D s) γ d D s n ω ≤ M) :
    1 - ω ≤ R.sampleProb M fun X ↦
      R.RecoversStrong ζ (alg11 thr ⟨n, sampleList X, ζ, γ, d, D, s⟩) := by
  by_cases hω1 : 1 < ω
  · exact (by linarith : 1 - ω ≤ 0).trans (sampleProb_nonneg R M _)
  push Not at hω1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine le_trans ?_ (sampleProb_mono R M (Q := fun _ ↦ True) fun X _ u ↦ u.elim0)
    rw [sampleProb_true]
    linarith
  have hζ' : (0 : ℝ) < ζ := by exact_mod_cast hζ
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hτ := tauPrime_pos (D := D) (s := s) (mul_pos hζ' (eta_pos γ hD s)).ne' hγ' hd
  refine prob_of_accurate R hτ hγ'.le hn hω hω1 hM _ fun X hM1 hacc ↦ ?_
  obtain ⟨t₂, t₃, hthr_eq, ht₂1, ht₂2, ht₃1, ht₃2⟩ :=
    hthr n (sampleList X) ζ γ d D s ω hn hζ hγ hd hD hω hω1
      (by rw [length_sampleList]; exact hM)
  intro u
  have hwf := wellFormed_sampleList hM1 X ζ γ d D s
  have hout := prune11 R hζ' hγ' hd hD hW hL hDeg hs u _ t₂ t₃ ht₂1 ht₂2 ht₃1 ht₃2 (hacc u)
  have hget : outNbhd (alg11 thr ⟨n, sampleList X, ζ, γ, d, D, s⟩) u =
      (greedy (fun I S ↦ empNuL (sampleList X) n u I S) n u (2 ^ s) t₂).filter (fun i ↦
        (candList n u (2 ^ s) ((greedy (fun I S ↦ empNuL (sampleList X) n u I S) n u (2 ^ s)
          t₂).erase i)).any fun l ↦ decide (t₃ < empNuL (sampleList X) n u l.toFinset
            ((greedy (fun I S ↦ empNuL (sampleList X) n u I S) n u (2 ^ s) t₂).erase i))) := by
    simp only [alg11, ite_eq_left hwf, hthr_eq, outNbhd]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range u.2]
    simp
  rw [hget]
  exact hout

end BB20.Learning
