module

public import BHSV25.Planted.Expander
public import BHSV25.Planted.Brute
public import BHSV25.Planted.Prob

/-!
# Small uncolored components

The probabilistic part of [BHSV25, Lemma B.21]. A set `S` of vertices of the host is **stuck**
under the colors `χ` (`BHSV25.Planted.Stuck`) if every `v ∈ S` misses a color `a ≠ χ(v)` among its
neighbors outside `S`; the components of the uncolored vertices after safe recoloring are stuck.

* **One stuck set** (`BHSV25.Planted.card_stuck_le`, the paper's Claim): giving every vertex of
  the boundary `∂S` one neighbor in `S`, the colors of `S` and `∂S` each avoid one prescribed color,
  so at most `(k - 1)^|S| ((k - 1) / k)^|∂S| k^n` colorings make `S` stuck.
* **The connected sets through a vertex** (`BHSV25.Planted.sum_weight_le_one`): for `p + q = 1`,
  `∑_S p^|S| q^|∂S| ≤ 1` over the connected sets `S ∋ v₀`, as the events "`S ⊆ X` and `∂S ∩ X = ∅`"
  of a random set `X` with independent `p`-coins are disjoint: they say that `S` is the component
  of `v₀` in `X`. This replaces the paper's count `n binom(t₁ + t₂, t₁)` of the components with
  `t₁` vertices and `t₂` boundary vertices (Lemma B.23 of David and Feige).
* **No large stuck set** (`BHSV25.Planted.card_bad_stuck_le`): if every connected set of at most
  `β n` vertices has at least `X₀ |S|` boundary vertices with `X₀ ≥ 4 k⁶` (Lemma 7.19), then with
  `p = 1 / (2k)` each such `S` with `k^|S| > n²` is stuck on at most `n⁻⁶ p^|S| q^|∂S| k^n`
  colorings, so some one is stuck on at most `k^n / n⁵` colorings.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Finset

variable {H : Graph} {k : ℕ}

/-- `S` is **stuck** under `χ`: every vertex of `S` misses a color other than its own among its
neighbors outside `S`. -/
def Stuck (H : Graph) (S : Finset (Fin H.1)) (χ : Fin H.1 → Fin k) : Prop :=
  ∀ v ∈ S, ∃ a : Fin k, a ≠ χ v ∧ ∀ y : Fin H.1, H.2.Adj v y → y ∉ S → χ y ≠ a

/-! ### Avoiding prescribed colors -/

open Classical in
/-- The colorings in which every vertex of `W` avoids its prescribed color: `(k - 1)^|W| k^(n-|W|)`
of them. -/
theorem card_avoid (n : ℕ) (W : Finset (Fin n)) (f : Fin n → Fin k) :
    (univ.filter fun χ : Fin n → Fin k ↦ ∀ y ∈ W, χ y ≠ f y).card =
      (k - 1) ^ W.card * k ^ (n - W.card) := by
  have h : (univ.filter fun χ : Fin n → Fin k ↦ ∀ y ∈ W, χ y ≠ f y) =
      Fintype.piFinset fun y ↦ if y ∈ W then univ.erase (f y) else univ := by
    ext χ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h y
      split_ifs with hy
      · exact mem_erase.2 ⟨h y hy, mem_univ _⟩
      · exact mem_univ _
    · intro h y hy
      have := h y
      rw [ite_eq_left hy] at this
      exact (mem_erase.1 this).1
  rw [h, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  rw [prod_ite, prod_const, prod_const]
  congr 2
  · rw [filter_mem_eq_inter, univ_inter]
  · rw [filter_not, filter_mem_eq_inter, univ_inter, card_sdiff_of_subset (subset_univ _),
      card_univ, Fintype.card_fin]

open Classical in
/-- **One stuck set** [BHSV25, Claim in the proof of Lemma B.21]. -/
theorem card_stuck_le (hk : 0 < k) (S : Finset (Fin H.1)) :
    ((univ.filter fun χ : Fin H.1 → Fin k ↦ Stuck H S χ).card : ℝ) ≤
      ((k : ℝ) - 1) ^ S.card * (((k : ℝ) - 1) / k) ^ (boundary H S).card * (k : ℝ) ^ H.1 := by
  set D := boundary H S with hD
  have hown : ∀ y ∈ D, ∃ u ∈ S, H.2.Adj u y := fun y hy ↦ (mem_filter.1 hy).2.2
  -- a neighbor in `S` of every boundary vertex
  set o : Fin H.1 → Fin H.1 := fun y ↦ if h : y ∈ D then Classical.choose (hown y h) else y
  have ho : ∀ y ∈ D, o y ∈ S ∧ H.2.Adj (o y) y := fun y hy ↦ by
    simp only [o, dite_eq_left hy]; exact Classical.choose_spec (hown y hy)
  -- the prescribed colors from a choice `a` of missing colors on `S`
  set f : ({v // v ∈ S} → Fin k) → Fin H.1 → Fin k := fun a y ↦
    if hy : y ∈ S then a ⟨y, hy⟩ else if hy' : y ∈ D then a ⟨o y, (ho y hy').1⟩ else ⟨0, hk⟩
  have hdisj : Disjoint S D := disjoint_left.2 fun u hu hb ↦ (mem_filter.1 hb).2.1 hu
  set W := S ∪ D
  have hsub : (univ.filter fun χ : Fin H.1 → Fin k ↦ Stuck H S χ) ⊆
      (univ : Finset ({v // v ∈ S} → Fin k)).biUnion fun a ↦
        univ.filter fun χ : Fin H.1 → Fin k ↦ ∀ y ∈ W, χ y ≠ f a y := by
    intro χ hχ
    rw [mem_filter] at hχ
    have hst := hχ.2
    set a : {v // v ∈ S} → Fin k := fun v ↦ Classical.choose (hst v.1 v.2)
    have ha : ∀ v : {v // v ∈ S}, a v ≠ χ v ∧
        ∀ y : Fin H.1, H.2.Adj v y → y ∉ S → χ y ≠ a v := fun v ↦
      Classical.choose_spec (hst v.1 v.2)
    rw [mem_biUnion]
    refine ⟨a, mem_univ _, mem_filter.2 ⟨mem_univ _, fun y hy ↦ ?_⟩⟩
    rcases mem_union.1 hy with hyS | hyD
    · simp only [f, dite_eq_left hyS]
      exact fun h ↦ (ha ⟨y, hyS⟩).1 h.symm
    · have hyS : y ∉ S := (mem_filter.1 hyD).2.1
      simp only [f, dite_eq_right hyS, dite_eq_left hyD]
      exact (ha ⟨o y, (ho y hyD).1⟩).2 y (ho y hyD).2 hyS
  have hcard := (card_le_card hsub).trans card_biUnion_le
  simp only [card_avoid] at hcard
  rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin,
    smul_eq_mul] at hcard
  have hW : W.card = S.card + D.card := card_union_of_disjoint hdisj
  have hWn : W.card ≤ H.1 := by
    have := card_le_univ W; rwa [Fintype.card_fin] at this
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcast : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  calc ((univ.filter fun χ : Fin H.1 → Fin k ↦ Stuck H S χ).card : ℝ)
      ≤ ((k ^ S.card * ((k - 1) ^ W.card * k ^ (H.1 - W.card)) : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = ((k : ℝ) - 1) ^ S.card * (((k : ℝ) - 1) / k) ^ D.card * (k : ℝ) ^ H.1 := by
        push_cast
        rw [hcast, hW, pow_add, div_pow]
        have hkn : (k : ℝ) ^ H.1 = (k : ℝ) ^ (H.1 - (S.card + D.card)) * (k : ℝ) ^ S.card *
            (k : ℝ) ^ D.card := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        rw [hkn]
        have hk0 : (k : ℝ) ≠ 0 := by positivity
        field_simp

/-! ### The connected sets through a vertex -/

open Classical in
/-- The sets `X` containing `S` and disjoint from its boundary. -/
noncomputable def coverSets (H : Graph) (S : Finset (Fin H.1)) : Finset (Finset (Fin H.1)) :=
  (univ : Finset (Fin H.1)).powerset.filter fun X ↦ S ⊆ X ∧ Disjoint X (boundary H S)

open Classical in
/-- Two connected sets through `v₀` have no common covering set unless they are equal. -/
theorem eq_of_mem_coverSets {S S' X : Finset (Fin H.1)} {v₀ : Fin H.1} (hS : v₀ ∈ S)
    (hS' : v₀ ∈ S') (hc : ConnSet H.2 S) (hc' : ConnSet H.2 S') (hX : X ∈ coverSets H S)
    (hX' : X ∈ coverSets H S') : S = S' := by
  rw [coverSets, mem_filter] at hX hX'
  have key : ∀ {A B : Finset (Fin H.1)}, v₀ ∈ A → v₀ ∈ B → ConnSet H.2 A → A ⊆ X →
      Disjoint X (boundary H B) → A ⊆ B := by
    intro A B hA hB hcA hAX hXB
    by_contra hnot
    have hsub : A ∩ B ⊆ A := inter_subset_left
    have hne : (A ∩ B).Nonempty := ⟨v₀, mem_inter.2 ⟨hA, hB⟩⟩
    have hneq : A ∩ B ≠ A := fun h ↦ hnot (h ▸ inter_subset_right)
    obtain ⟨u, hu, w, hw, hwAB, huw⟩ := hcA (A ∩ B) hsub hne hneq
    have hwB : w ∉ B := fun h ↦ hwAB (mem_inter.2 ⟨hw, h⟩)
    have hwb : w ∈ boundary H B := mem_filter.2 ⟨mem_univ _, hwB, u, (mem_inter.1 hu).2, huw⟩
    exact disjoint_left.1 hXB (hAX hw) hwb
  exact Subset.antisymm (key hS hS' hc hX.2.1 hX'.2.2) (key hS' hS hc' hX'.2.1 hX.2.2)

open Classical in
/-- The weight of the covering sets of `S`: `p^|S| q^|∂S|`. -/
theorem sum_coverSets (S : Finset (Fin H.1)) {p q : ℝ} (hpq : p + q = 1) :
    ∑ X ∈ coverSets H S, p ^ X.card * q ^ (H.1 - X.card) =
      p ^ S.card * q ^ (boundary H S).card := by
  set D := boundary H S
  set R := univ \ (S ∪ D) with hR
  have hdisj : Disjoint S D := disjoint_left.2 fun u hu hb ↦ (mem_filter.1 hb).2.1 hu
  have hn : H.1 = S.card + D.card + R.card := by
    rw [hR, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
      card_union_of_disjoint hdisj]
    have := card_le_univ (S ∪ D)
    rw [Fintype.card_fin, card_union_of_disjoint hdisj] at this
    omega
  have himg : coverSets H S = R.powerset.image fun Y ↦ S ∪ Y := by
    ext X
    rw [coverSets, mem_filter, mem_image]
    constructor
    · rintro ⟨-, hSX, hXD⟩
      refine ⟨X \ S, mem_powerset.2 fun y hy ↦ ?_, union_sdiff_of_subset hSX⟩
      rw [mem_sdiff] at hy
      rw [hR, mem_sdiff, mem_union]
      exact ⟨mem_univ _, fun h ↦ h.elim hy.2 (disjoint_left.1 hXD hy.1)⟩
    · rintro ⟨Y, hY, rfl⟩
      rw [mem_powerset] at hY
      refine ⟨mem_powerset.2 (subset_univ _), subset_union_left, disjoint_union_left.2
        ⟨hdisj, disjoint_left.2 fun y hy hyD ↦ ?_⟩⟩
      have := hY hy
      rw [hR, mem_sdiff, mem_union] at this
      exact this.2 (Or.inr hyD)
  have hinj : Set.InjOn (fun Y ↦ S ∪ Y) (R.powerset : Set (Finset (Fin H.1))) := by
    intro Y hY Y' hY' h
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hY hY'
    have hYS : Disjoint Y S := disjoint_left.2 fun y hy hyS ↦ by
      have := hY hy; rw [hR, mem_sdiff, mem_union] at this; exact this.2 (Or.inl hyS)
    have hY'S : Disjoint Y' S := disjoint_left.2 fun y hy hyS ↦ by
      have := hY' hy; rw [hR, mem_sdiff, mem_union] at this; exact this.2 (Or.inl hyS)
    have h1 : (S ∪ Y) \ S = Y := by rw [union_sdiff_left, sdiff_eq_self_of_disjoint hYS]
    have h2 : (S ∪ Y') \ S = Y' := by rw [union_sdiff_left, sdiff_eq_self_of_disjoint hY'S]
    simp only at h
    rw [← h1, ← h2, h]
  rw [himg, sum_image hinj]
  have hterm : ∀ Y ∈ R.powerset, p ^ (S ∪ Y).card * q ^ (H.1 - (S ∪ Y).card) =
      p ^ S.card * q ^ D.card * (p ^ Y.card * q ^ (R.card - Y.card)) := by
    intro Y hY
    rw [mem_powerset] at hY
    have hYS : Disjoint S Y := disjoint_left.2 fun y hyS hy ↦ by
      have := hY hy; rw [hR, mem_sdiff, mem_union] at this; exact this.2 (Or.inl hyS)
    have hYR := card_le_card hY
    rw [card_union_of_disjoint hYS, show H.1 - (S.card + Y.card) = D.card + (R.card - Y.card)
      by omega, pow_add, pow_add]
    ring
  rw [sum_congr rfl hterm, ← mul_sum, sum_pow_mul_eq_add_pow, hpq, one_pow, mul_one]

open Classical in
/-- **The connected sets through a vertex**: `∑_S p^|S| q^|∂S| ≤ 1` for `p, q ≥ 0`, `p + q = 1`. -/
theorem sum_weight_le_one (F : Finset (Finset (Fin H.1))) {v₀ : Fin H.1}
    (hF : ∀ S ∈ F, v₀ ∈ S ∧ ConnSet H.2 S) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    ∑ S ∈ F, p ^ S.card * q ^ (boundary H S).card ≤ 1 := by
  have hdisj : (F : Set (Finset (Fin H.1))).PairwiseDisjoint (coverSets H) := by
    intro S hS S' hS' hne
    refine disjoint_left.2 fun X hX hX' ↦ hne ?_
    exact eq_of_mem_coverSets (hF S hS).1 (hF S' hS').1 (hF S hS).2 (hF S' hS').2 hX hX'
  calc ∑ S ∈ F, p ^ S.card * q ^ (boundary H S).card
      = ∑ S ∈ F, ∑ X ∈ coverSets H S, p ^ X.card * q ^ (H.1 - X.card) :=
        sum_congr rfl fun S _ ↦ (sum_coverSets S hpq).symm
    _ = ∑ X ∈ F.biUnion (coverSets H), p ^ X.card * q ^ (H.1 - X.card) :=
        (sum_biUnion hdisj).symm
    _ ≤ ∑ X ∈ (univ : Finset (Fin H.1)).powerset, p ^ X.card * q ^ (H.1 - X.card) := by
        refine sum_le_sum_of_subset_of_nonneg (fun X _ ↦ mem_powerset.2 (subset_univ _))
          fun _ _ _ ↦ by positivity
    _ = 1 := by
        have := sum_pow_mul_eq_add_pow p q (univ : Finset (Fin H.1))
        rw [card_univ, Fintype.card_fin, hpq, one_pow] at this
        exact this

/-! ### No large stuck set -/

/-- `(1 - a)^m ≤ 1 / (1 + m a)` for `0 ≤ a ≤ 1`. -/
theorem one_sub_pow_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (m : ℕ) :
    (1 - a) ^ m ≤ 1 / (1 + m * a) := by
  have h1 : 1 + m * a ≤ (1 + a) ^ m := one_add_mul_le_pow (by linarith) m
  have h2 : (1 - a) ^ m * (1 + a) ^ m ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  rw [le_div_iff₀ (by positivity)]
  have h3 : 0 ≤ (1 - a) ^ m := pow_nonneg (by linarith) m
  nlinarith

/-- The base `2 k (k - 1) (2 (k - 1) / (2k - 1))^X₀ ≤ 1 / k³` for `X₀ ≥ 4 k⁶`. -/
theorem stuck_base_le (hk : 1 ≤ k) {X₀ : ℕ} (hX₀ : 4 * k ^ 6 ≤ X₀) :
    2 * (k : ℝ) * ((k : ℝ) - 1) * (2 * ((k : ℝ) - 1) / (2 * k - 1)) ^ X₀ ≤ 1 / (k : ℝ) ^ 3 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hX : (4 : ℝ) * (k : ℝ) ^ 6 ≤ X₀ := by exact_mod_cast hX₀
  set a : ℝ := 1 / (2 * k - 1) with ha
  have h2k : (0 : ℝ) < 2 * k - 1 := by linarith
  have hr : 2 * ((k : ℝ) - 1) / (2 * k - 1) = 1 - a := by rw [ha]; field_simp; ring
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one h2k]; linarith
  rw [hr]
  have h1 := one_sub_pow_le ha0 ha1 X₀
  have h3 : 1 / (1 + X₀ * a) ≤ 2 * k / X₀ := by
    have hX0 : (0 : ℝ) < X₀ := lt_of_lt_of_le (by positivity) hX
    rw [div_le_div_iff₀ (by positivity) hX0, ha]
    field_simp
    nlinarith
  have h4 : 0 ≤ 2 * (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
  calc 2 * (k : ℝ) * ((k : ℝ) - 1) * (1 - a) ^ X₀ ≤ 2 * k * ((k : ℝ) - 1) * (2 * k / X₀) :=
        mul_le_mul_of_nonneg_left (h1.trans h3) h4
    _ ≤ 1 / (k : ℝ) ^ 3 := by
        have hX0 : (0 : ℝ) < X₀ := lt_of_lt_of_le (by positivity) hX
        rw [div_le_div_iff₀ (by positivity) (by positivity)] at *
        rw [mul_div_assoc', div_le_div_iff₀ hX0 (by positivity)]
        nlinarith [pow_le_pow_left₀ zero_le_one hk1 3, pow_le_pow_left₀ zero_le_one hk1 4]

open Classical in
/-- **A large stuck set is unlikely**: a connected `S` with `k^|S| > n²` and `|∂S| ≥ X₀ |S|` is
stuck on at most `n⁻⁶ p^|S| q^|∂S| k^n` colorings, for `p = 1 / (2k)`, `q = 1 - p`. -/
theorem card_stuck_le_weight (hk : 1 ≤ k) (hn : 0 < H.1) {X₀ : ℕ} (hX₀ : 4 * k ^ 6 ≤ X₀)
    (S : Finset (Fin H.1))
    (hbd : X₀ * S.card ≤ (boundary H S).card) (hbig : H.1 ^ 2 < k ^ S.card) :
    ((univ.filter fun χ : Fin H.1 → Fin k ↦ Stuck H S χ).card : ℝ) ≤
      1 / (H.1 : ℝ) ^ 6 * ((1 / (2 * k)) ^ S.card * (1 - 1 / (2 * k)) ^ (boundary H S).card) *
        (k : ℝ) ^ H.1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine (card_stuck_le (by omega) S).trans ?_
  set s := S.card
  set b := (boundary H S).card
  set p : ℝ := 1 / (2 * k)
  set q : ℝ := 1 - 1 / (2 * k)
  set r : ℝ := 2 * ((k : ℝ) - 1) / (2 * k - 1) with hrdef
  have h2k : (0 : ℝ) < 2 * k - 1 := by linarith
  have h2k' : (2 * (k : ℝ) - 1) ≠ 0 := h2k.ne'
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hr0 : 0 ≤ r := by rw [hrdef]; apply div_nonneg <;> linarith
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one h2k]; linarith
  have hfac : ((k : ℝ) - 1) ^ s * (((k : ℝ) - 1) / k) ^ b =
      (2 * k * ((k : ℝ) - 1)) ^ s * r ^ b * (p ^ s * q ^ b) := by
    have e1 : ((k : ℝ) - 1) = 2 * k * ((k : ℝ) - 1) * p := by
      simp only [p]; field_simp
    have e2 : ((k : ℝ) - 1) / k = r * q := by
      have hq' : q = (2 * k - 1) / (2 * k) := by simp only [q]; field_simp
      rw [hq', hrdef, div_mul_div_comm, eq_div_iff (mul_ne_zero h2k' (by positivity))]
      field_simp
    rw [e2, mul_pow]
    conv_lhs => rw [e1]
    rw [mul_pow]
    ring
  rw [hfac]
  have hb : r ^ b ≤ r ^ (X₀ * s) := pow_le_pow_of_le_one hr0 hr1 hbd
  have hbase := stuck_base_le hk hX₀
  rw [← hrdef] at hbase
  have hmain : (2 * k * ((k : ℝ) - 1)) ^ s * r ^ b ≤ 1 / (H.1 : ℝ) ^ 6 := by
    have h0 : 0 ≤ 2 * (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
    calc (2 * k * ((k : ℝ) - 1)) ^ s * r ^ b ≤ (2 * k * ((k : ℝ) - 1)) ^ s * r ^ (X₀ * s) :=
          mul_le_mul_of_nonneg_left hb (pow_nonneg h0 _)
      _ = (2 * k * ((k : ℝ) - 1) * r ^ X₀) ^ s := by rw [mul_pow _ (r ^ X₀), ← pow_mul]
      _ ≤ (1 / (k : ℝ) ^ 3) ^ s := pow_le_pow_left₀ (by positivity) hbase s
      _ = 1 / ((k : ℝ) ^ s) ^ 3 := by rw [div_pow, one_pow, ← pow_mul, ← pow_mul, mul_comm]
      _ ≤ 1 / (H.1 : ℝ) ^ 6 := by
          have h1 : ((H.1 : ℝ) ^ 2) < (k : ℝ) ^ s := by exact_mod_cast hbig
          have h2 : ((H.1 : ℝ) ^ 2) ^ 3 ≤ ((k : ℝ) ^ s) ^ 3 :=
            pow_le_pow_left₀ (by positivity) h1.le 3
          rw [← pow_mul] at h2
          exact one_div_le_one_div_of_le (by positivity) h2
  have hpq : 0 ≤ p ^ s * q ^ b := by
    have : 0 ≤ q := by simp only [q]; rw [sub_nonneg, div_le_one (by positivity)]; linarith
    positivity
  have hkn : (0 : ℝ) ≤ (k : ℝ) ^ H.1 := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmain hpq) hkn

open Classical in
/-- **No large stuck set** [BHSV25, Lemma B.21, probabilistic part]: if the connected sets of at
most `β n` vertices expand by `X₀ ≥ 4 k⁶`, some connected set of at most `β n` vertices with
`k^|S| > n²` is stuck on at most `k^n / n⁵` colorings. -/
theorem card_bad_stuck_le (hk : 1 ≤ k) {X₀ : ℕ} (hX₀ : 4 * k ^ 6 ≤ X₀) {β : ℝ}
    (hexp : ∀ S : Finset (Fin H.1), ConnSet H.2 S → (S.card : ℝ) ≤ β * H.1 →
      X₀ * S.card ≤ (boundary H S).card) :
    ((univ.filter fun χ : Fin H.1 → Fin k ↦ ∃ S : Finset (Fin H.1), S.Nonempty ∧
        ConnSet H.2 S ∧ (S.card : ℝ) ≤ β * H.1 ∧ H.1 ^ 2 < k ^ S.card ∧ Stuck H S χ).card : ℝ) ≤
      (k : ℝ) ^ H.1 / (H.1 : ℝ) ^ 5 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set F : Fin H.1 → Finset (Finset (Fin H.1)) := fun v₀ ↦
    (univ : Finset (Fin H.1)).powerset.filter fun S ↦ v₀ ∈ S ∧ ConnSet H.2 S ∧
      (S.card : ℝ) ≤ β * H.1 ∧ H.1 ^ 2 < k ^ S.card
  have hsub : (univ.filter fun χ : Fin H.1 → Fin k ↦ ∃ S : Finset (Fin H.1), S.Nonempty ∧
        ConnSet H.2 S ∧ (S.card : ℝ) ≤ β * H.1 ∧ H.1 ^ 2 < k ^ S.card ∧ Stuck H S χ) ⊆
      (univ : Finset (Fin H.1)).biUnion fun v₀ ↦ (F v₀).biUnion fun S ↦
        univ.filter fun χ : Fin H.1 → Fin k ↦ Stuck H S χ := by
    intro χ hχ
    rw [mem_filter] at hχ
    obtain ⟨S, ⟨v₀, hv₀⟩, hc, hβ, hbig, hst⟩ := hχ.2
    rw [mem_biUnion]
    refine ⟨v₀, mem_univ _, mem_biUnion.2 ⟨S, ?_, mem_filter.2 ⟨mem_univ _, hst⟩⟩⟩
    exact mem_filter.2 ⟨mem_powerset.2 (subset_univ _), hv₀, hc, hβ, hbig⟩
  have hper : ∀ v₀, (((F v₀).biUnion fun S ↦
      univ.filter fun χ : Fin H.1 → Fin k ↦ Stuck H S χ).card : ℝ) ≤
      1 / (H.1 : ℝ) ^ 6 * (k : ℝ) ^ H.1 := by
    intro v₀
    have hq0 : 0 ≤ 1 - 1 / (2 * (k : ℝ)) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    calc (((F v₀).biUnion fun S ↦ univ.filter fun χ : Fin H.1 → Fin k ↦ Stuck H S χ).card : ℝ)
        ≤ ∑ S ∈ F v₀, ((univ.filter fun χ : Fin H.1 → Fin k ↦ Stuck H S χ).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ S ∈ F v₀, 1 / (H.1 : ℝ) ^ 6 * ((1 / (2 * (k : ℝ))) ^ S.card *
            (1 - 1 / (2 * (k : ℝ))) ^ (boundary H S).card) * (k : ℝ) ^ H.1 := by
          refine sum_le_sum fun S hS ↦ ?_
          rw [mem_filter] at hS
          exact card_stuck_le_weight hk (Fin.pos v₀) hX₀ S (hexp S hS.2.2.1 hS.2.2.2.1)
            hS.2.2.2.2
      _ = 1 / (H.1 : ℝ) ^ 6 * (∑ S ∈ F v₀, (1 / (2 * (k : ℝ))) ^ S.card *
            (1 - 1 / (2 * (k : ℝ))) ^ (boundary H S).card) * (k : ℝ) ^ H.1 := by
          simp only [Finset.mul_sum, Finset.sum_mul]
      _ ≤ 1 / (H.1 : ℝ) ^ 6 * 1 * (k : ℝ) ^ H.1 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
            (by positivity)
          exact sum_weight_le_one (F v₀) (v₀ := v₀) (p := 1 / (2 * (k : ℝ)))
            (q := 1 - 1 / (2 * (k : ℝ)))
            (fun S hS ↦ ⟨(mem_filter.1 hS).2.1, (mem_filter.1 hS).2.2.1⟩) (by positivity) hq0
            (by ring)
      _ = 1 / (H.1 : ℝ) ^ 6 * (k : ℝ) ^ H.1 := by ring
  calc _ ≤ (((univ : Finset (Fin H.1)).biUnion fun v₀ ↦ (F v₀).biUnion fun S ↦
          univ.filter fun χ : Fin H.1 → Fin k ↦ Stuck H S χ).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ v₀ : Fin H.1, (((F v₀).biUnion fun S ↦
          univ.filter fun χ : Fin H.1 → Fin k ↦ Stuck H S χ).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _v₀ : Fin H.1, 1 / (H.1 : ℝ) ^ 6 * (k : ℝ) ^ H.1 := sum_le_sum fun v₀ _ ↦ hper v₀
    _ = (k : ℝ) ^ H.1 / (H.1 : ℝ) ^ 5 := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rcases Nat.eq_zero_or_pos H.1 with h | h
        · rw [h]; simp
        have : (0 : ℝ) < H.1 := by exact_mod_cast h
        field_simp

end Planted

end BHSV25
