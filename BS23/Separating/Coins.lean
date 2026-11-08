module

public import BS23.Model
public import Background.Sampling

/-!
# A random pivot from coins

The algorithm of [BS23, Theorem 1.1] picks its pivot among the `n` sample points from its coins:
the number given by the first `b` coins (`Sampling.chunkVal b l 0`), modulo `n`
(`BS23.Separating.coinIdx`). The first `b` coins are uniform on `Fin 2^b` (`Sampling.sum_chunks`)
and each residue modulo `n` comes from at most `2^b/n + 1` of these numbers
(`BS23.Separating.card_filter_mod_eq_le`), so a set `Bad` of pivots is hit with probability at
most `|Bad|/n + n/2^b` (`BS23.Separating.le_coinProb_of_coinIdx`).
-/

@[expose] public section

namespace BS23.Separating

open Finset

/-- The **pivot index** read from the coins `l`: the number given by the first `b` bits of `l`,
modulo `n`. -/
def coinIdx (n b : ℕ) (l : List Bool) : ℕ := Sampling.chunkVal b l 0 % n

theorem coinIdx_lt {n : ℕ} (hn : 0 < n) (b : ℕ) (l : List Bool) : coinIdx n b l < n :=
  Nat.mod_lt _ hn

/-- The pivot index only reads the first `b` coins. -/
theorem coinIdx_take {n b m : ℕ} (h : b ≤ m) (l : List Bool) :
    coinIdx n b (l.take m) = coinIdx n b l := by
  unfold coinIdx Sampling.chunkVal
  congr 1
  refine sum_congr rfl fun t ht ↦ ?_
  have hlt : 0 * b + t < m := by
    have := mem_range.1 ht
    omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hlt]

/-- **Fibres of `· % n`**: at most `N/n + 1` numbers below `N` have a given residue. -/
theorem card_filter_mod_eq_le (N n i : ℕ) :
    (univ.filter fun u : Fin N ↦ (u : ℕ) % n = i).card ≤ N / n + 1 := by
  have h := card_le_card_of_injOn (s := univ.filter fun u : Fin N ↦ (u : ℕ) % n = i)
    (t := range (N / n + 1)) (fun u ↦ (u : ℕ) / n) ?_ ?_
  · simpa using h
  · intro u _
    have := Nat.div_le_div_right (c := n) u.2.le
    simp only [coe_range, Set.mem_Iio]
    omega
  · intro u hu u' hu' huu
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hu hu'
    have huu' : (u : ℕ) / n = (u' : ℕ) / n := huu
    apply Fin.ext
    rw [← Nat.div_add_mod (u : ℕ) n, ← Nat.div_add_mod (u' : ℕ) n, huu', hu, hu']

/-- At most `|B| (N/n + 1)` numbers below `N` have their residue modulo `n` in `B`. -/
theorem card_filter_mod_mem_le (N n : ℕ) (B : Finset ℕ) :
    (univ.filter fun u : Fin N ↦ (u : ℕ) % n ∈ B).card ≤ B.card * (N / n + 1) := by
  rw [card_eq_sum_card_fiberwise (f := fun u : Fin N ↦ (u : ℕ) % n)
    (s := univ.filter fun u : Fin N ↦ (u : ℕ) % n ∈ B) (t := B) fun u hu ↦ (mem_filter.1 hu).2]
  calc ∑ i ∈ B, ((univ.filter fun u : Fin N ↦ (u : ℕ) % n ∈ B).filter
          fun u : Fin N ↦ (u : ℕ) % n = i).card
      ≤ ∑ _i ∈ B, (N / n + 1) := sum_le_sum fun i _ ↦
        (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans
          (card_filter_mod_eq_le N n i)
    _ = B.card * (N / n + 1) := by rw [sum_const, smul_eq_mul]

open Classical in
/-- **A random pivot avoids a bad set.** If a property `P` of coin strings of length `m ≥ b`
holds whenever the pivot index `coinIdx n b` is not in `Bad`, then it has probability at least
`1 - |Bad|/n - n/2^b`. -/
theorem le_coinProb_of_coinIdx {m n b : ℕ} (hb : b ≤ m) (hn : 0 < n) (Bad : Finset (Fin n))
    {P : List Bool → Prop}
    (hP : ∀ l : List Bool, l.length = m → ∀ p : Fin n, (p : ℕ) = coinIdx n b l → p ∉ Bad → P l) :
    1 - (Bad.card : ℝ) / n - n / 2 ^ b ≤ coinProb m P := by
  set B : Finset ℕ := Bad.map Fin.valEmbedding with hB
  set N := 2 ^ b with hN
  -- The coin strings whose first chunk avoids `B` modulo `n` satisfy `P`.
  have hgood : ∀ c : Fin m → Bool, Sampling.chunkVal b (List.ofFn c) 0 % n ∉ B →
      P (List.ofFn c) := by
    intro c hc
    refine hP _ (List.length_ofFn) ⟨coinIdx n b (List.ofFn c), coinIdx_lt hn _ _⟩ rfl
      fun hmem ↦ hc ?_
    rw [hB, mem_map]
    exact ⟨_, hmem, rfl⟩
  have hsum := Sampling.sum_chunks (T := m) (N := 1) (b := b) (by simpa using hb)
    (fun v ↦ if v 0 % n ∉ B then (1 : ℝ) else 0)
  simp only [Fin.val_zero] at hsum
  have hle : (∑ c : Fin m → Bool,
      if Sampling.chunkVal b (List.ofFn c) 0 % n ∉ B then (1 : ℝ) else 0) ≤
      (Fintype.card {r : Fin m → Bool // P (List.ofFn r)} : ℝ) := by
    rw [Fintype.card_subtype, natCast_card_filter]
    refine sum_le_sum fun c _ ↦ ?_
    by_cases hc : Sampling.chunkVal b (List.ofFn c) 0 % n ∈ B
    · simp only [hc, not_true_eq_false, ite_false]
      split_ifs <;> norm_num
    · simp [hc, hgood c hc]
  -- The good first chunks.
  have hone : (∑ u : Fin 1 → Fin N, if ((u 0 : Fin N) : ℕ) % n ∉ B then (1 : ℝ) else 0) =
      ((univ.filter fun u : Fin N ↦ (u : ℕ) % n ∉ B).card : ℝ) := by
    rw [natCast_card_filter]
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin N)) _ _ fun _ ↦ rfl
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin N)))
    (fun u : Fin N ↦ (u : ℕ) % n ∈ B)
  rw [card_univ, Fintype.card_fin] at hsplit
  have hbad := card_filter_mod_mem_le N n B
  have hBcard : B.card = Bad.card := card_map _
  have hBn : Bad.card ≤ n := by simpa using card_le_univ Bad
  -- Real arithmetic.
  have hNpos : (0 : ℝ) < N := by positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiv : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / n := Nat.cast_div_le
  have hsplit' : ((univ.filter fun u : Fin N ↦ (u : ℕ) % n ∈ B).card : ℝ) +
      ((univ.filter fun u : Fin N ↦ (u : ℕ) % n ∉ B).card : ℝ) = N := by
    exact_mod_cast hsplit
  have hbad' : ((univ.filter fun u : Fin N ↦ (u : ℕ) % n ∈ B).card : ℝ) ≤
      Bad.card * ((N : ℝ) / n + 1) := by
    have h1 : ((univ.filter fun u : Fin N ↦ (u : ℕ) % n ∈ B).card : ℝ) ≤
        Bad.card * ((N / n : ℕ) + 1 : ℝ) := by
      rw [← hBcard]
      exact_mod_cast hbad
    have h2 : (Bad.card : ℝ) * ((N / n : ℕ) + 1 : ℝ) ≤ Bad.card * ((N : ℝ) / n + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hgoodCard : (N : ℝ) - Bad.card * ((N : ℝ) / n + 1) ≤
      ((univ.filter fun u : Fin N ↦ (u : ℕ) % n ∉ B).card : ℝ) := by linarith
  have hcard : (2 : ℝ) ^ (m - 1 * b) * ((N : ℝ) - Bad.card * ((N : ℝ) / n + 1)) ≤
      (Fintype.card {r : Fin m → Bool // P (List.ofFn r)} : ℝ) := by
    have h := hle
    rw [hsum, hone] at h
    exact (mul_le_mul_of_nonneg_left hgoodCard (by positivity)).trans h
  unfold coinProb
  have h2m : (2 : ℝ) ^ m = 2 ^ (m - 1 * b) * N := by
    rw [hN, Nat.cast_pow, Nat.cast_ofNat, ← pow_add, one_mul, Nat.sub_add_cancel hb]
  rw [le_div_iff₀ (by positivity), h2m]
  have hBn' : (Bad.card : ℝ) ≤ n := by exact_mod_cast hBn
  have hkey : (1 - (Bad.card : ℝ) / n - n / N) * N ≤ (N : ℝ) - Bad.card * ((N : ℝ) / n + 1) := by
    have e1 : (1 - (Bad.card : ℝ) / n - n / N) * N = N - Bad.card * (N / n) - n := by
      field_simp
    have e2 : (N : ℝ) - Bad.card * ((N : ℝ) / n + 1) = N - Bad.card * (N / n) - Bad.card := by
      ring
    rw [e1, e2]
    linarith
  calc (1 - (Bad.card : ℝ) / n - n / 2 ^ b) * (2 ^ (m - 1 * b) * N)
      = 2 ^ (m - 1 * b) * ((1 - (Bad.card : ℝ) / n - n / N) * N) := by
        rw [hN, Nat.cast_pow, Nat.cast_ofNat]
        ring
    _ ≤ 2 ^ (m - 1 * b) * ((N : ℝ) - Bad.card * ((N : ℝ) / n + 1)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ _ := hcard

end BS23.Separating
