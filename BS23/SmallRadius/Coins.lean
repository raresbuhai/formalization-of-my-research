module

public import BS23.Model
public import Background.Sampling

/-!
# Coins of the small-radius algorithm

The algorithm of [BS23, Theorem 1.3] runs `k` rounds; round `r` reads the `r`-th block of `b`
coins, the bits at positions `r b, …, (r + 1) b - 1` (`BS23.SmallRadius.blockNat`), and uses the
number `u < 2^b` they encode to pick a pivot.

* **Weighted pick.** For weights `ω ≥ 0` on `Fin N` with total `Z > 0`, `pick ω b u` is the least
  `i` with `u Z < 2^b ∑_{i' ≤ i} ω i'` (`BS23.SmallRadius.pick`; computable for rational weights).
  Each index is picked by at most `2^b ω i / Z + 1` numbers `u < 2^b`
  (`BS23.SmallRadius.card_pick_eq_le`), so the average of `f ≥ 0` over `u` is at most its
  average under `ω` plus `N max f / 2^b` (`BS23.SmallRadius.avg_pick_le`,
  `BS23.SmallRadius.card_pick_mem_le`).
* **Sequential union bound.** If round `r` fails with probability at most `δ` over its block of
  coins, whatever the earlier blocks are (as long as no earlier round failed), then all `k` rounds
  succeed with probability at least `1 - k δ` (`BS23.SmallRadius.coinProb_seq`, and the version
  for failures that read their block through `blockNat`, `BS23.SmallRadius.coinProb_seq_blockNat`).
-/

@[expose] public section

namespace BS23.SmallRadius

open Finset

/-! ### Blocks of coins -/

/-- The number encoded by the bits of `c` at positions `r b, …, (r + 1) b - 1` (least significant
first; missing bits count as `false`). -/
def blockNat (c : List Bool) (b r : ℕ) : ℕ := Sampling.chunkVal b c r

theorem sum_range_ite_pow_lt (f : ℕ → Bool) (b : ℕ) :
    ∑ t ∈ range b, (if f t then 2 ^ t else 0) < 2 ^ b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [sum_range_succ, pow_succ]
    have : (if f b then 2 ^ b else 0) ≤ 2 ^ b := by split_ifs <;> simp
    omega

theorem blockNat_lt (c : List Bool) (b r : ℕ) : blockNat c b r < 2 ^ b :=
  sum_range_ite_pow_lt (fun t ↦ c.getD (r * b + t) false) b

/-- The `r`-th block only reads the first `(r + 1) b` bits. -/
theorem blockNat_take {c : List Bool} {b r m : ℕ} (h : (r + 1) * b ≤ m) :
    blockNat (c.take m) b r = blockNat c b r := by
  unfold blockNat Sampling.chunkVal
  refine sum_congr rfl fun t ht ↦ ?_
  have hlt : r * b + t < m := by
    have h1 := mem_range.1 ht
    have h2 : (r + 1) * b = r * b + b := by ring
    omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hlt]

/-- After a prefix of `r b` bits, the `r`-th block is the first block of the rest. -/
theorem blockNat_append {p l : List Bool} {b r : ℕ} (hp : p.length = r * b) :
    blockNat (p ++ l) b r = blockNat l b 0 := by
  unfold blockNat Sampling.chunkVal
  refine sum_congr rfl fun t _ ↦ ?_
  rw [List.getD_append_right _ _ _ _ (by omega), hp, zero_mul, zero_add, Nat.add_sub_cancel_left]

/-! ### A weighted pick -/

section Pick

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {N : ℕ}

/-- The partial sum `∑_{i < n} ω i`. -/
def partialW (ω : Fin N → K) (n : ℕ) : K := ∑ i ∈ univ.filter (fun i : Fin N ↦ (i : ℕ) < n), ω i

/-- The **weighted pick**: the least `i` with `u Z < 2^b ∑_{i' ≤ i} ω i'`, where `Z = ∑ ω`
(`0` if there is none). For `u` uniform below `2^b`, it is `i` with probability about
`ω i / Z`. -/
def pick [NeZero N] (ω : Fin N → K) (b u : ℕ) : Fin N :=
  (Fin.find? fun i ↦ decide ((u : K) * ∑ j, ω j < 2 ^ b * partialW ω (i + 1))).getD 0

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem partialW_zero (ω : Fin N → K) : partialW ω 0 = 0 := by
  simp [partialW]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem partialW_succ (ω : Fin N → K) (i : Fin N) :
    partialW ω (i + 1) = partialW ω i + ω i := by
  have : (univ.filter fun j : Fin N ↦ (j : ℕ) < i + 1) =
      insert i (univ.filter fun j : Fin N ↦ (j : ℕ) < i) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  rw [partialW, partialW, this, sum_insert (by simp), add_comm]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem partialW_self (ω : Fin N → K) : partialW ω N = ∑ j, ω j := by
  rw [partialW, filter_true_of_mem fun j _ ↦ j.isLt]

/-- **The pick lands in its interval**: for `u < 2^b`,
`2^b ∑_{i < pick} ω i ≤ u Z < 2^b ∑_{i ≤ pick} ω i`. -/
theorem pick_spec [NeZero N] {ω : Fin N → K} (hZ : 0 < ∑ j, ω j) {b u : ℕ} (hu : u < 2 ^ b) :
    2 ^ b * partialW ω (pick ω b u) ≤ (u : K) * ∑ j, ω j ∧
      (u : K) * ∑ j, ω j < 2 ^ b * partialW ω (pick ω b u + 1) := by
  set p : Fin N → Bool := fun i ↦ decide ((u : K) * ∑ j, ω j < 2 ^ b * partialW ω (i + 1))
    with hp
  have hN : 0 < N := NeZero.pos N
  have hex : ∃ i, p i := by
    refine ⟨⟨N - 1, by omega⟩, ?_⟩
    have hN1 : N - 1 + 1 = N := by omega
    simp only [hp, hN1, partialW_self, decide_eq_true_eq]
    have hu' : (u : K) < 2 ^ b := by exact_mod_cast hu
    exact mul_lt_mul_of_pos_right hu' hZ
  have hpick : pick ω b u = Fin.find (p ·) hex := by
    rw [pick, ← hp, Fin.find?_eq_some_find_of_exists hex, Option.getD_some]
  have hspec : p (pick ω b u) = true := hpick ▸ Fin.find_spec hex
  have hmin : ∀ j : Fin N, j < pick ω b u → ¬ p j = true := fun j hj ↦
    Fin.find_min hex (hpick ▸ hj)
  refine ⟨?_, by simpa [hp] using hspec⟩
  by_cases h0 : (pick ω b u : ℕ) = 0
  · rw [h0, partialW_zero, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hZ.le
  · have hj : (⟨(pick ω b u : ℕ) - 1, by omega⟩ : Fin N) < pick ω b u :=
      Fin.mk_lt_of_lt_val (by omega)
    have := hmin _ hj
    have hj1 : (pick ω b u : ℕ) - 1 + 1 = pick ω b u := by omega
    simpa [hp, hj1] using this

/-- **Each index is picked by few numbers**: at most `2^b ω i / Z + 1` numbers `u < 2^b`. -/
theorem card_pick_eq_le [NeZero N] {ω : Fin N → K} (hω : ∀ i, 0 ≤ ω i) (hZ : 0 < ∑ j, ω j)
    (b : ℕ) (i : Fin N) :
    ((#{u : Fin (2 ^ b) | pick ω b u = i} : ℕ) : K) ≤ 2 ^ b * ω i / ∑ j, ω j + 1 := by
  set s := univ.filter fun u : Fin (2 ^ b) ↦ pick ω b u = i with hs
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he, card_empty, Nat.cast_zero]
    have := hω i
    positivity
  set m := s.min' hne
  set M := s.max' hne
  have hmM : m ≤ M := min'_le_max' s hne
  have hsub : s ⊆ Icc m M := fun u hu ↦ mem_Icc.2 ⟨min'_le s u hu, le_max' s u hu⟩
  have hcard : s.card ≤ (M : ℕ) + 1 - m := by
    have := card_le_card hsub
    rwa [Fin.card_Icc] at this
  have hm := (mem_filter.1 (min'_mem s hne)).2
  have hM := (mem_filter.1 (max'_mem s hne)).2
  have h1 := (pick_spec hZ (b := b) (u := m) m.isLt).1
  have h2 := (pick_spec hZ (b := b) (u := M) M.isLt).2
  rw [hm] at h1
  rw [hM, partialW_succ] at h2
  -- `(M - m) Z < 2^b ω i`.
  have hlt : ((M : ℕ) - (m : ℕ) : K) < 2 ^ b * ω i / ∑ j, ω j := by
    rw [lt_div_iff₀ hZ]
    nlinarith
  have hmM' : (m : ℕ) ≤ (M : ℕ) := hmM
  calc ((s.card : ℕ) : K) ≤ (((M : ℕ) + 1 - m : ℕ) : K) := by exact_mod_cast hcard
    _ = ((M : ℕ) - (m : ℕ) : K) + 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
        ring
    _ ≤ 2 ^ b * ω i / ∑ j, ω j + 1 := by linarith

/-- **Sums over the pick.** For `f ≥ 0`,
`∑_{u < 2^b} f (pick u) ≤ 2^b (∑ ω f) / Z + ∑ f`. -/
theorem sum_pick_le [NeZero N] {ω : Fin N → K} (hω : ∀ i, 0 ≤ ω i) (hZ : 0 < ∑ j, ω j)
    (b : ℕ) {f : Fin N → K} (hf : ∀ i, 0 ≤ f i) :
    ∑ u : Fin (2 ^ b), f (pick ω b u) ≤
      2 ^ b * (∑ i, ω i * f i) / (∑ j, ω j) + ∑ i, f i := by
  rw [← sum_fiberwise univ (fun u : Fin (2 ^ b) ↦ pick ω b u) (fun u ↦ f (pick ω b u))]
  have hfib : ∀ i : Fin N, ∑ u ∈ univ.filter (fun u : Fin (2 ^ b) ↦ pick ω b u = i),
      f (pick ω b u) = ((#{u : Fin (2 ^ b) | pick ω b u = i} : ℕ) : K) * f i := by
    intro i
    rw [sum_congr rfl fun u hu ↦ by rw [(mem_filter.1 hu).2], sum_const, nsmul_eq_mul]
  simp_rw [hfib]
  calc ∑ i : Fin N, ((#{u : Fin (2 ^ b) | pick ω b u = i} : ℕ) : K) * f i
      ≤ ∑ i : Fin N, (2 ^ b * ω i / ∑ j, ω j + 1) * f i :=
        sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (card_pick_eq_le hω hZ b i) (hf i)
    _ = 2 ^ b * (∑ i, ω i * f i) / (∑ j, ω j) + ∑ i, f i := by
        rw [mul_sum, sum_div, ← sum_add_distrib]
        refine sum_congr rfl fun i _ ↦ ?_
        ring

/-- **Averages over the pick.** For `0 ≤ f ≤ F`, the average of `f (pick u)` over `u < 2^b` is at
most the `ω`-average of `f` plus `N F / 2^b`. -/
theorem avg_pick_le [NeZero N] {ω : Fin N → K} (hω : ∀ i, 0 ≤ ω i) (hZ : 0 < ∑ j, ω j)
    (b : ℕ) {f : Fin N → K} {F : K} (hf : ∀ i, 0 ≤ f i) (hfF : ∀ i, f i ≤ F) :
    (∑ u : Fin (2 ^ b), f (pick ω b u)) / 2 ^ b ≤
      (∑ i, ω i * f i) / (∑ j, ω j) + N * F / 2 ^ b := by
  have hsum : ∑ i, f i ≤ N * F := by
    calc ∑ i, f i ≤ ∑ _i : Fin N, F := sum_le_sum fun i _ ↦ hfF i
      _ = N * F := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2b : (0 : K) < 2 ^ b := by positivity
  rw [div_le_iff₀ h2b]
  calc ∑ u : Fin (2 ^ b), f (pick ω b u)
      ≤ 2 ^ b * (∑ i, ω i * f i) / (∑ j, ω j) + ∑ i, f i := sum_pick_le hω hZ b hf
    _ ≤ 2 ^ b * (∑ i, ω i * f i) / (∑ j, ω j) + N * F := by linarith
    _ = ((∑ i, ω i * f i) / (∑ j, ω j) + N * F / 2 ^ b) * 2 ^ b := by
        field_simp

/-- **A pick avoids a light set.** At most `2^b ω(S) / Z + |S|` numbers `u < 2^b` pick an index
in `S`. -/
theorem card_pick_mem_le [NeZero N] {ω : Fin N → K} (hω : ∀ i, 0 ≤ ω i) (hZ : 0 < ∑ j, ω j)
    (b : ℕ) (S : Finset (Fin N)) :
    ((#{u : Fin (2 ^ b) | pick ω b u ∈ S} : ℕ) : K) ≤
      2 ^ b * (∑ i ∈ S, ω i) / (∑ j, ω j) + #S := by
  have h := sum_pick_le hω hZ b (f := fun i ↦ if i ∈ S then (1 : K) else 0)
    fun i ↦ by split_ifs <;> norm_num
  beta_reduce at h
  have e1 : ∑ u : Fin (2 ^ b), (if pick ω b u ∈ S then (1 : K) else 0) =
      ((#{u : Fin (2 ^ b) | pick ω b u ∈ S} : ℕ) : K) := (natCast_card_filter _ _).symm
  have e2 : ∑ i, ω i * (if i ∈ S then (1 : K) else 0) = ∑ i ∈ S, ω i := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter, filter_mem_eq_inter, univ_inter]
  have e3 : ∑ i : Fin N, (if i ∈ S then (1 : K) else 0) = #S := by
    rw [← natCast_card_filter, filter_mem_eq_inter, univ_inter]
  rwa [e1, e2, e3] at h

end Pick

/-! ### Coin probabilities as sums -/

theorem coinProb_eq_sum (m : ℕ) (P : List Bool → Prop) [DecidablePred P] :
    coinProb m P = (∑ c : Fin m → Bool, if P (List.ofFn c) then (1 : ℝ) else 0) / 2 ^ m := by
  unfold coinProb
  rw [Fintype.card_subtype, natCast_card_filter]

theorem coinProb_nonneg (m : ℕ) (P : List Bool → Prop) : 0 ≤ coinProb m P := by
  unfold coinProb
  positivity

/-- Strings of `m + n` bits are a string of `m` bits followed by a string of `n` bits. -/
theorem sum_ofFn_append {m n : ℕ} (F : List Bool → ℝ) :
    ∑ c : Fin (m + n) → Bool, F (List.ofFn c) =
      ∑ p : Fin m → Bool, ∑ w : Fin n → Bool, F (List.ofFn p ++ List.ofFn w) := by
  rw [← (Fin.appendEquiv m n).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun p _ ↦ sum_congr rfl fun w _ ↦ ?_
  change F (List.ofFn (Fin.append p w)) = _
  rw [List.ofFn_fin_append]

/-- A function of the first `m` bits sums to `2^(T - m)` times its sum over strings of `m` bits. -/
theorem sum_ofFn_of_take {T m : ℕ} (hm : m ≤ T) (F : List Bool → ℝ)
    (hF : ∀ c : List Bool, F c = F (c.take m)) :
    ∑ c : Fin T → Bool, F (List.ofFn c) = 2 ^ (T - m) * ∑ w : Fin m → Bool, F (List.ofFn w) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [sum_ofFn_append, Nat.add_sub_cancel_left, mul_sum]
  refine sum_congr rfl fun p _ ↦ ?_
  have : ∀ w : Fin n → Bool, F (List.ofFn p ++ List.ofFn w) = F (List.ofFn p) := fun w ↦ by
    rw [hF, List.take_left' List.length_ofFn]
  simp only [this, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

open Classical in
/-- An event of the first `m ≤ T` coins has the same probability among strings of `T` coins. -/
theorem coinProb_take {T m : ℕ} (hm : m ≤ T) (P : List Bool → Prop)
    (hP : ∀ c, P c ↔ P (c.take m)) : coinProb T P = coinProb m P := by
  have hs := sum_ofFn_of_take hm (fun l ↦ if P l then (1 : ℝ) else 0) fun c ↦ by
    simp only [hP c]
  beta_reduce at hs
  rw [coinProb_eq_sum, coinProb_eq_sum, hs]
  have h2 : (2 : ℝ) ^ T = 2 ^ (T - m) * 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel hm]
  rw [h2, mul_div_mul_left _ _ (by positivity)]

open Classical in
theorem coinProb_add_compl (T : ℕ) (P Q : List Bool → Prop) :
    coinProb T P = coinProb T (fun c ↦ P c ∧ Q c) + coinProb T (fun c ↦ P c ∧ ¬ Q c) := by
  simp only [coinProb_eq_sum, ← add_div, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun c _ ↦ ?_
  by_cases hP : P (List.ofFn c) <;> by_cases hQ : Q (List.ofFn c) <;> simp [hP, hQ]

/-! ### The sequential union bound -/

open Classical in
/-- **The failure of one round.** Under the hypotheses of `coinProb_seq` for `k + 1` rounds, the
probability that the first `k` rounds succeed and round `k` fails is at most `δ`. -/
theorem coinProb_last_le {k b T : ℕ} (hT : (k + 1) * b ≤ T) {δ : ℝ} (hδ : 0 ≤ δ)
    (Bad : ℕ → List Bool → Prop)
    (hloc : ∀ r < k + 1, ∀ c, Bad r c ↔ Bad r (c.take ((r + 1) * b)))
    (hstep : ∀ p : List Bool, p.length = k * b → (∀ r' < k, ¬ Bad r' p) →
      coinProb b (fun w ↦ Bad k (p ++ w)) ≤ δ) :
    coinProb T (fun c ↦ (∀ r < k, ¬ Bad r c) ∧ Bad k c) ≤ δ := by
  have hkb : (k + 1) * b = k * b + b := by ring
  -- Round `r ≤ k` only reads the first `m ≥ (r + 1) b` bits.
  have hread : ∀ r < k + 1, ∀ m, (r + 1) * b ≤ m → ∀ c : List Bool,
      Bad r c ↔ Bad r (c.take m) := by
    intro r hr m hm c
    rw [hloc r hr c, hloc r hr (c.take m), List.take_take, min_eq_left hm]
  set H : List Bool → Prop := fun c ↦ (∀ r < k, ¬ Bad r c) ∧ Bad k c with hH
  have hHtake : ∀ c, H c ↔ H (c.take (k * b + b)) := by
    intro c
    simp only [hH]
    refine and_congr (forall₂_congr fun r hr ↦ not_congr (hread r (by omega) _ ?_ c))
      (hread k (by omega) _ hkb.le c)
    have : (r + 1) * b ≤ (k + 1) * b := Nat.mul_le_mul_right _ (by omega)
    omega
  have hs := sum_ofFn_append (m := k * b) (n := b) fun l ↦ if H l then (1 : ℝ) else 0
  beta_reduce at hs
  rw [coinProb_take (hkb ▸ hT) H hHtake, coinProb_eq_sum, hs]
  -- Each prefix contributes at most `δ 2^b`.
  have hpre : ∀ p : Fin (k * b) → Bool,
      ∑ w : Fin b → Bool, (if H (List.ofFn p ++ List.ofFn w) then (1 : ℝ) else 0) ≤ δ * 2 ^ b := by
    intro p
    have hG : ∀ w : Fin b → Bool, (∀ r < k, ¬ Bad r (List.ofFn p ++ List.ofFn w)) ↔
        ∀ r < k, ¬ Bad r (List.ofFn p) := by
      intro w
      refine forall₂_congr fun r hr ↦ not_congr ?_
      have hrk : (r + 1) * b ≤ k * b := Nat.mul_le_mul_right _ (by omega)
      rw [hread r (by omega) _ hrk, List.take_left' List.length_ofFn]
    by_cases hp : ∀ r < k, ¬ Bad r (List.ofFn p)
    · have h := hstep (List.ofFn p) List.length_ofFn hp
      rw [coinProb_eq_sum, div_le_iff₀ (by positivity)] at h
      refine le_of_eq_of_le (sum_congr rfl fun w _ ↦ ?_) h
      have hiff : H (List.ofFn p ++ List.ofFn w) ↔ Bad k (List.ofFn p ++ List.ofFn w) := by
        simp only [hH]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨(hG w).2 hp, h⟩⟩
      exact if_congr hiff rfl rfl
    · have : ∀ w : Fin b → Bool, ¬ H (List.ofFn p ++ List.ofFn w) := fun w hw ↦
        hp ((hG w).1 hw.1)
      simp only [this, ite_false, sum_const_zero]
      positivity
  calc (∑ p : Fin (k * b) → Bool, ∑ w : Fin b → Bool,
        (if H (List.ofFn p ++ List.ofFn w) then (1 : ℝ) else 0)) / 2 ^ (k * b + b)
      ≤ (∑ _p : Fin (k * b) → Bool, δ * 2 ^ b) / 2 ^ (k * b + b) := by
        gcongr with p
        exact hpre p
    _ = δ := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
          nsmul_eq_mul, pow_add]
        push_cast
        field_simp

/-- **Sequential union bound over blocks of coins.** Let `k b ≤ T` and let `Bad r` (`r < k`) be
the failure of round `r`, which only reads the first `(r + 1) b` coins. If, after any prefix of
`r b` coins on which no earlier round fails, round `r` fails for at most a `δ` fraction of the next
`b` coins, then all `k` rounds succeed with probability at least `1 - k δ`. -/
theorem coinProb_seq {k b T : ℕ} (hT : k * b ≤ T) {δ : ℝ} (Bad : ℕ → List Bool → Prop)
    (hloc : ∀ r < k, ∀ c, Bad r c ↔ Bad r (c.take ((r + 1) * b)))
    (hstep : ∀ r < k, ∀ p : List Bool, p.length = r * b → (∀ r' < r, ¬ Bad r' p) →
      coinProb b (fun w ↦ Bad r (p ++ w)) ≤ δ) :
    1 - k * δ ≤ coinProb T (fun c ↦ ∀ r < k, ¬ Bad r c) := by
  classical
  induction k with
  | zero =>
    have h1 : coinProb T (fun c ↦ ∀ r < 0, ¬ Bad r c) = 1 := by
      rw [coinProb_eq_sum]
      simp only [Nat.not_lt_zero, false_imp_iff, implies_true, ite_true, sum_const, card_univ,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one]
      push_cast
      exact div_self (by positivity)
    rw [h1]
    simp
  | succ k ih =>
    have hkT : k * b ≤ T := (Nat.mul_le_mul_right _ (Nat.le_succ k)).trans hT
    have ih' := ih hkT (fun r hr ↦ hloc r (by omega)) (fun r hr ↦ hstep r (by omega))
    have hδ : 0 ≤ δ :=
      (coinProb_nonneg _ _).trans (hstep 0 (by omega) [] (by simp) (by simp))
    have hlast := coinProb_last_le hT hδ Bad hloc (hstep k (by omega))
    have hsplit := coinProb_add_compl T (fun c ↦ ∀ r < k, ¬ Bad r c) (Bad k)
    have heq : coinProb T (fun c ↦ ∀ r < k + 1, ¬ Bad r c) =
        coinProb T (fun c ↦ (∀ r < k, ¬ Bad r c) ∧ ¬ Bad k c) := by
      congr 1
      funext c
      apply propext
      constructor
      · intro h
        exact ⟨fun r hr ↦ h r (by omega), h k (by omega)⟩
      · rintro ⟨h, hk⟩ r hr
        rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
        · exact h r hr
        · exact hk
    rw [heq]
    push_cast
    linarith

/-- The first block of `b` coins is uniform on `Fin 2^b`. -/
theorem coinProb_blockNat (b : ℕ) (Q : ℕ → Prop) :
    coinProb b (fun w ↦ Q (blockNat w b 0)) = (Nat.card {u : Fin (2 ^ b) // Q u} : ℝ) / 2 ^ b := by
  classical
  rw [coinProb_eq_sum]
  have hsum := Sampling.sum_chunks (T := b) (N := 1) (b := b) (by simp)
    (fun v ↦ if Q (v 0) then (1 : ℝ) else 0)
  simp only [Fin.val_zero] at hsum
  have hone : (∑ u : Fin 1 → Fin (2 ^ b), if Q ((u 0 : Fin (2 ^ b)) : ℕ) then (1 : ℝ) else 0) =
      (Nat.card {u : Fin (2 ^ b) // Q u} : ℝ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, natCast_card_filter]
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin (2 ^ b))) _ _ fun _ ↦ rfl
  rw [show (fun c : Fin b → Bool ↦ if Q (blockNat (List.ofFn c) b 0) then (1 : ℝ) else 0) =
      fun c ↦ if Q (Sampling.chunkVal b (List.ofFn c) 0) then (1 : ℝ) else 0 from rfl]
  rw [hsum, hone, one_mul, Nat.sub_self, pow_zero, one_mul]

/-- **Sequential union bound, block form.** Let `k b ≤ T`, and let round `r < k` fail when
`B r p u` holds, where `p` is the first `r b` coins and `u` the number encoded by the `r`-th block
(`blockNat`). If, after any prefix `p` of `r b` coins on which no earlier round fails, at most
`δ 2^b` numbers `u < 2^b` make round `r` fail, then all `k` rounds succeed with probability at
least `1 - k δ`. -/
theorem coinProb_seq_blockNat {k b T : ℕ} (hT : k * b ≤ T) {δ : ℝ}
    (B : ℕ → List Bool → ℕ → Prop)
    (hstep : ∀ r < k, ∀ p : List Bool, p.length = r * b →
      (∀ r' < r, ¬ B r' (p.take (r' * b)) (blockNat p b r')) →
      (Nat.card {u : Fin (2 ^ b) // B r p u} : ℝ) ≤ δ * 2 ^ b) :
    1 - k * δ ≤ coinProb T (fun c ↦ ∀ r < k, ¬ B r (c.take (r * b)) (blockNat c b r)) := by
  refine coinProb_seq hT (fun r c ↦ B r (c.take (r * b)) (blockNat c b r)) ?_ ?_
  · intro r _ c
    have h : r * b ≤ (r + 1) * b := Nat.mul_le_mul_right _ (Nat.le_succ r)
    rw [List.take_take, min_eq_left h, blockNat_take le_rfl]
  · intro r hr p hp hprev
    have hfun : (fun w ↦ B r ((p ++ w).take (r * b)) (blockNat (p ++ w) b r)) =
        fun w ↦ B r p (blockNat w b 0) := by
      funext w
      rw [List.take_left' hp, blockNat_append hp]
    rw [hfun, coinProb_blockNat, div_le_iff₀ (by positivity)]
    exact hstep r hr p hp hprev

end BS23.SmallRadius
