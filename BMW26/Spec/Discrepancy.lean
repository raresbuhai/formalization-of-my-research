module

public import BMW26.Spec.Defs

/-!
# Discrepancy between sets of good vertices

[BMW26, Lemma 5.3]: with probability at least `1 - 1/m³`, for all disjoint sets `S, T` of good
vertices, `|w(S, T) - p Q(S, T)| ≤ η p m √(|S||T|)` (`BMW26.disc_whp`). More generally, for
`p ≥ 2048 (q + 1) log m / (η⁴ m)` the failure probability is at most `1/m^q`
(`BMW26.disc_whp_pow`).

The proof (`BMW26.Disc.disc_of_cand`) splits `S ∪ T` along a part with no hypercube edge to the
rest (`BMW26.Disc.cutW_split`, then `∑ᵢ √(|Sᵢ||Tᵢ|) ≤ √(|S||T|)`), until the union is
connected (`BMW26.Disc.Conn`). For a connected `W = A ∪ B`:

* **imbalanced** `|A|/|B| ∉ [η²/16, 16/η²]` (`BMW26.Disc.imbalanced`): deterministic, since
  good vertices have degree at most `2 p m`;
* **small** `|W| < m` (`BMW26.Disc.small`): deterministic, by the edge isoperimetry of the
  hypercube, `Q_m[W]` has at most `|W| ln |W|` edges (`BMW26.Disc.ein_le`, by induction on the
  dimension);
* **large and balanced** (`BMW26.Disc.Cand`): Bernstein's inequality fails with probability at
  most `2 m^(-12 (q + 1) |W|)` (`BMW26.Disc.prob_bad`), and there are at most
  `2^m m^(2(t-1)) 2^t` such pairs with `|W| = t` (`BMW26.Disc.card_cands_le`: a connected set is
  the vertex set of a closed walk of length `2 (|W| - 1)`, `BMW26.Disc.exists_walk`); a union
  bound over `t ≥ m` concludes (`BMW26.Disc.sum_cands_le`).

The events of the union bound are indexed by the pairs `(A, B)` only, not by the bad vertices.
-/

@[expose] public section

namespace BMW26

open Finset

variable {m : ℕ}

namespace Disc

/-- Reindexing by `flip · i` between the two half-cubes of direction `i`. -/
theorem sum_flip_false (i : Fin m) (G : Cube m → ℝ) :
    ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), G (flip x i) =
      ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = true), G x := by
  apply Finset.sum_nbij' (flip · i) (flip · i)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [flip_apply_self, hx]; rfl
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [flip_apply_self, hx]; rfl
  · intro x _; exact flip_flip x i
  · intro x _; exact flip_flip x i
  · intro x _; rfl

/-- Sums over the edges of direction `i`, read at their lower endpoints, of a quantity at both
endpoints, are sums over all vertices. -/
theorem sum_lower (F : Cube m → ℝ) (i : Fin m) :
    ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), (F x + F (flip x i)) = ∑ x, F x := by
  rw [sum_add_distrib, sum_flip_false,
    ← sum_filter_add_sum_filter_not univ (fun x : Cube m ↦ x i = false)]
  congr 1
  apply sum_congr _ (fun _ _ ↦ rfl)
  ext x
  simp

theorem cutW_comm (w : Fin m → Cube m → ℝ) (S T : Finset (Cube m)) :
    cutW w S T = cutW w T S := by
  unfold cutW
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun x _ ↦ ?_
  congr 1
  exact if_congr or_comm rfl rfl

@[simp] theorem cutW_empty_left (w : Fin m → Cube m → ℝ) (T : Finset (Cube m)) :
    cutW w ∅ T = 0 := by
  simp [cutW]

@[simp] theorem cutW_empty_right (w : Fin m → Cube m → ℝ) (S : Finset (Cube m)) :
    cutW w S ∅ = 0 := by
  simp [cutW]

theorem cutW_nonneg {w : Fin m → Cube m → ℝ} (hw : ∀ i x, 0 ≤ w i x)
    (S T : Finset (Cube m)) : 0 ≤ cutW w S T := by
  unfold cutW
  refine sum_nonneg fun i _ ↦ sum_nonneg fun x _ ↦ mul_nonneg (hw i x) ?_
  split_ifs <;> norm_num

theorem cutW_le_cutW_one {w : Fin m → Cube m → ℝ} (hw : ∀ i x, w i x ≤ 1)
    (S T : Finset (Cube m)) : cutW w S T ≤ cutW 1 S T := by
  unfold cutW
  refine sum_le_sum fun i _ ↦ sum_le_sum fun x _ ↦ ?_
  split_ifs <;> simp [hw i x]

theorem deg_one (x : Cube m) : deg 1 x = m := by
  simp [deg]

/-- The weight of the edges between `S` and `T` is at most the total degree of `S`. -/
theorem cutW_le_sum_deg {w : Fin m → Cube m → ℝ} (hw : ∀ i x, 0 ≤ w i x)
    (S T : Finset (Cube m)) : cutW w S T ≤ ∑ x ∈ S, deg w x := by
  classical
  have h1 : ∑ x ∈ S, deg w x =
      ∑ i, ∑ x, if x ∈ S then w i (lowPt x i) else 0 := by
    rw [sum_comm, ← sum_filter_add_sum_filter_not univ (· ∈ S)]
    simp only [deg]
    rw [sum_eq_zero (s := univ.filter (· ∉ S)) (fun x hx ↦ ?_), add_zero]
    · apply sum_congr (by ext; simp) fun x hx ↦ ?_
      simp only [mem_filter, mem_univ, true_and] at hx
      simp [hx]
    · simp only [mem_filter, mem_univ, true_and] at hx
      simp [hx]
  rw [h1]
  unfold cutW
  refine sum_le_sum fun i _ ↦ ?_
  rw [← sum_lower]
  refine sum_le_sum fun x hx ↦ ?_
  simp only [mem_filter, mem_univ, true_and] at hx
  rw [lowPt_flip, lowPt_of_false hx]
  have := hw i x
  split_ifs <;> simp_all

/-- If no edge of `Q_m` joins `V` to the rest of `S ∪ T`, the cut splits along `V`. -/
theorem cutW_split (w : Fin m → Cube m → ℝ) (S T V : Finset (Cube m))
    (hV : ∀ x ∈ S ∪ T, ∀ i, flip x i ∈ S ∪ T → (x ∈ V ↔ flip x i ∈ V)) :
    cutW w S T = cutW w (S ∩ V) (T ∩ V) + cutW w (S \ V) (T \ V) := by
  unfold cutW
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [← mul_add]
  congr 1
  have key := hV x
  simp only [mem_union] at key
  simp only [mem_inter, mem_sdiff]
  by_cases hxV : x ∈ V <;> by_cases hfV : flip x i ∈ V <;>
    by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;>
    by_cases hfS : flip x i ∈ S <;> by_cases hfT : flip x i ∈ T <;> simp_all

open Classical in
/-- Twice the number of edges of `Q_m` inside `W`: the pairs `(x, i)` with `x` and `flip x i` in
`W`. -/
noncomputable def ein (W : Finset (Cube m)) : ℝ :=
  ∑ x, ∑ i, if x ∈ W ∧ flip x i ∈ W then 1 else 0

theorem sum_cube_succ (f : Cube (m + 1) → ℝ) :
    ∑ x, f x = ∑ y : Cube m, f (Fin.cons false y) + ∑ y : Cube m, f (Fin.cons true y) := by
  rw [← (Fin.consEquiv fun _ ↦ Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    add_comm]
  rfl

theorem flip_cons_zero (b : Bool) (y : Cube m) :
    flip (Fin.cons b y : Cube (m + 1)) 0 = Fin.cons (!b) y := by
  simp [flip, Fin.update_cons_zero]

theorem flip_cons_succ (b : Bool) (y : Cube m) (j : Fin m) :
    flip (Fin.cons b y : Cube (m + 1)) j.succ = Fin.cons b (flip y j) := by
  simp [flip, Fin.cons_update]

theorem card_eq_sum (W : Finset (Cube m)) :
    (W.card : ℝ) = ∑ x, if x ∈ W then 1 else 0 := by
  classical
  rw [sum_boole]
  congr 2
  ext; simp

/-- The real inequality behind the edge isoperimetry of the hypercube. -/
theorem mul_log_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * Real.log a + b * Real.log b + min a b ≤ (a + b) * Real.log (a + b) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [min_eq_left hb]
  rcases hb.eq_or_lt with rfl | hb
  · simp [min_eq_right ha.le]
  have hs : 0 < a + b := by linarith
  have h1 : b / (a + b) ≤ Real.log (a + b) - Real.log a := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hs ha)
    rw [Real.log_div hs.ne' ha.ne', inv_div] at this
    have e : 1 - a / (a + b) = b / (a + b) := by field_simp; ring
    linarith
  have h2 : a / (a + b) ≤ Real.log (a + b) - Real.log b := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hs hb)
    rw [Real.log_div hs.ne' hb.ne', inv_div] at this
    have e : 1 - b / (a + b) = a / (a + b) := by field_simp; ring
    linarith
  have h3 : min a b ≤ 2 * (a * b) / (a + b) := by
    rw [le_div_iff₀ hs]
    rcases le_total a b with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have e1 : a * (b / (a + b)) + b * (a / (a + b)) = 2 * (a * b) / (a + b) := by
    field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left h1 ha.le, mul_le_mul_of_nonneg_left h2 hb.le]

theorem natCast_mul_log_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * Real.log n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hn))

/-- **Edge isoperimetry of the hypercube** (with the natural logarithm): `Q_m[W]` has at most
`|W| log |W|` edges. -/
theorem ein_le : ∀ {m : ℕ} (W : Finset (Cube m)), ein W ≤ 2 * (W.card * Real.log W.card)
  | 0, W => by
    have : ein W = 0 := by simp [ein]
    rw [this]
    have := natCast_mul_log_nonneg W.card
    linarith
  | m + 1, W => by
    classical
    set W₀ : Finset (Cube m) := univ.filter fun y ↦ (Fin.cons false y : Cube (m + 1)) ∈ W
    set W₁ : Finset (Cube m) := univ.filter fun y ↦ (Fin.cons true y : Cube (m + 1)) ∈ W
    have hcard : (W.card : ℝ) = W₀.card + W₁.card := by
      rw [card_eq_sum, card_eq_sum, card_eq_sum, sum_cube_succ]
      simp [W₀, W₁]
    have hinter : ((W₀ ∩ W₁).card : ℝ) = ∑ y : Cube m,
        if (Fin.cons false y : Cube (m + 1)) ∈ W ∧ (Fin.cons true y : Cube (m + 1)) ∈ W
        then 1 else 0 := by
      rw [card_eq_sum]
      simp [W₀, W₁]
    have hein : ein W = ein W₀ + ein W₁ + 2 * (W₀ ∩ W₁).card := by
      rw [hinter]
      simp only [ein]
      rw [sum_cube_succ]
      simp only [Fin.sum_univ_succ, flip_cons_zero, flip_cons_succ, Bool.not_false,
        Bool.not_true, sum_add_distrib]
      simp only [W₀, W₁, mem_filter, mem_univ, true_and]
      have e : ∀ y : Cube m, (if (Fin.cons true y : Cube (m + 1)) ∈ W ∧
          (Fin.cons false y : Cube (m + 1)) ∈ W then (1 : ℝ) else 0) =
          if (Fin.cons false y : Cube (m + 1)) ∈ W ∧ (Fin.cons true y : Cube (m + 1)) ∈ W
          then 1 else 0 := fun y ↦ if_congr and_comm rfl rfl
      simp only [e]
      ring
    have hI : ((W₀ ∩ W₁).card : ℝ) ≤ min (W₀.card : ℝ) W₁.card := by
      rw [le_min_iff]
      exact ⟨by exact_mod_cast card_le_card inter_subset_left,
        by exact_mod_cast card_le_card inter_subset_right⟩
    have h0 := ein_le W₀
    have h1 := ein_le W₁
    have key := mul_log_add_le (Nat.cast_nonneg W₀.card) (Nat.cast_nonneg W₁.card)
    rw [hein, hcard]
    linarith

/-- `W` induces a connected subgraph of `Q_m`: every proper nonempty part of `W` has a hypercube
neighbour in the rest of `W`. -/
def Conn (W : Finset (Cube m)) : Prop :=
  ∀ V ⊆ W, V.Nonempty → V ≠ W → ∃ x ∈ V, ∃ i, flip x i ∈ W ∧ flip x i ∉ V

/-- The end of the walk from `x` along the directions `l`. -/
def wend (x : Cube m) (l : List (Fin m)) : Cube m := l.foldl flip x

/-- The vertex set of the walk from `x` along the directions `l`. -/
def wset : Cube m → List (Fin m) → Finset (Cube m)
  | x, [] => {x}
  | x, i :: l => insert x (wset (flip x i) l)

@[simp] theorem wend_nil (x : Cube m) : wend x [] = x := rfl

@[simp] theorem wend_cons (x : Cube m) (i : Fin m) (l : List (Fin m)) :
    wend x (i :: l) = wend (flip x i) l := rfl

theorem wend_append (x : Cube m) (l₁ l₂ : List (Fin m)) :
    wend x (l₁ ++ l₂) = wend (wend x l₁) l₂ := by
  simp [wend, List.foldl_append]

theorem mem_wset_self (x : Cube m) (l : List (Fin m)) : x ∈ wset x l := by
  cases l <;> simp [wset]

theorem wset_append (x : Cube m) (l₁ l₂ : List (Fin m)) :
    wset x (l₁ ++ l₂) = wset x l₁ ∪ wset (wend x l₁) l₂ := by
  induction l₁ generalizing x with
  | nil =>
    simp only [List.nil_append, wend_nil, wset]
    rw [singleton_union, insert_eq_of_mem (mem_wset_self x l₂)]
  | cons i l ih =>
    simp only [List.cons_append, wset, wend_cons, ih, insert_union]

theorem exists_of_mem_wset {x y : Cube m} {l : List (Fin m)} (h : y ∈ wset x l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ wend x l₁ = y := by
  induction l generalizing x with
  | nil =>
    simp only [wset, mem_singleton] at h
    exact ⟨[], [], rfl, h.symm⟩
  | cons i l ih =>
    simp only [wset, mem_insert] at h
    rcases h with rfl | h
    · exact ⟨[], i :: l, rfl, rfl⟩
    · obtain ⟨l₁, l₂, rfl, h'⟩ := ih h
      exact ⟨i :: l₁, l₂, rfl, h'⟩

/-- In a connected set `W`, for every `1 ≤ k ≤ |W|`, there is a closed walk of length `2 (k - 1)`
inside `W` visiting exactly `k` vertices (grown one detour `u → v → u` at a time, after rotating
the closed walk to start at `u`). -/
theorem exists_walk_aux {W : Finset (Cube m)} (hW : Conn W) (hne : W.Nonempty) :
    ∀ k, 1 ≤ k → k ≤ W.card → ∃ x l, l.length = 2 * (k - 1) ∧ wend x l = x ∧
      wset x l ⊆ W ∧ (wset x l).card = k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro _
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, [], rfl, rfl, by simp [wset, hx], by simp [wset]⟩
  | succ k hk ih =>
    intro hkW
    obtain ⟨x, l, hlen, hend, hsub, hcard⟩ := ih (by omega)
    have hne' : (wset x l).Nonempty := ⟨x, mem_wset_self x l⟩
    have hneq : wset x l ≠ W := by
      rintro h; rw [h] at hcard; omega
    obtain ⟨u, hu, i, hvW, hvV⟩ := hW _ hsub hne' hneq
    obtain ⟨l₁, l₂, rfl, hu₁⟩ := exists_of_mem_wset hu
    have hu₂ : wend u l₂ = x := by rw [← hu₁, ← wend_append, hend]
    refine ⟨flip u i, i :: (l₂ ++ l₁ ++ [i]), ?_, ?_, ?_⟩
    · simp only [List.length_cons, List.length_append, List.length_nil] at hlen ⊢
      omega
    · simp [wend_append, flip_flip, hu₂, hu₁]
    have hset : wset (flip u i) (i :: (l₂ ++ l₁ ++ [i])) =
        insert (flip u i) (wset x (l₁ ++ l₂)) := by
      simp only [wset, flip_flip, wset_append, wend_append, hu₂, hu₁]
      ext z
      simp only [mem_insert, mem_union, mem_singleton]
      have := mem_wset_self u l₂
      rcases eq_or_ne z u with rfl | hz
      · simp [this]
      · simp only [hz, false_or]
        tauto
    rw [hset]
    refine ⟨insert_subset hvW hsub, ?_⟩
    rw [card_insert_of_notMem hvV, hcard]

/-- A connected set `W` is the vertex set of a walk of length `2 (|W| - 1)`. -/
theorem exists_walk {W : Finset (Cube m)} (hW : Conn W) (hne : W.Nonempty) :
    ∃ x l, l.length = 2 * (W.card - 1) ∧ wset x l = W := by
  obtain ⟨x, l, hlen, -, hsub, hcard⟩ :=
    exists_walk_aux hW hne W.card (card_pos.2 hne) le_rfl
  exact ⟨x, l, hlen, eq_of_subset_of_card_le hsub hcard.ge⟩

/-- `A` and `B` are **balanced**: `|A| / |B| ∈ [η² / 16, 16 / η²]`. -/
def Bal (η : ℝ) (A B : Finset (Cube m)) : Prop :=
  η ^ 2 * B.card ≤ 16 * A.card ∧ η ^ 2 * A.card ≤ 16 * B.card

/-- The pairs handled by the union bound: disjoint, nonempty, balanced, with a connected union of
size at least `m`. -/
def Cand (η : ℝ) (A B : Finset (Cube m)) : Prop :=
  Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧ Conn (A ∪ B) ∧ Bal η A B ∧
    m ≤ (A ∪ B).card

theorem deg_le_of_notMem {w : Fin m → Cube m → ℝ} {p γ : ℝ} {x : Cube m}
    (hx : x ∉ badSet w p γ) : deg w x ≤ (1 + γ) * p * m := by
  simp only [badSet, mem_filter, mem_univ, true_and, not_lt] at hx
  have := (abs_le.1 hx).2
  linarith

/-- On good vertices, the discrepancy is at most `3 p m |A|`. -/
theorem abs_le_three {w : Fin m → Cube m → ℝ} (hw : ∀ i x, 0 ≤ w i x) {p γ : ℝ}
    (hp : 0 ≤ p) (hγ1 : γ ≤ 1) (A B : Finset (Cube m)) (hA : Disjoint A (badSet w p γ)) :
    |cutW w A B - p * cutW 1 A B| ≤ 3 * p * m * A.card := by
  have h1 := cutW_le_sum_deg hw A B
  have h2 : ∑ x ∈ A, deg w x ≤ A.card * ((1 + γ) * p * m) := by
    rw [← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ fun x hx ↦ deg_le_of_notMem (disjoint_left.1 hA hx)
  have h3 := cutW_le_sum_deg (w := 1) (fun _ _ ↦ zero_le_one) A B
  simp only [deg_one, sum_const, nsmul_eq_mul] at h3
  have h4 := cutW_nonneg hw A B
  have h5 := cutW_nonneg (w := 1) (fun _ _ ↦ zero_le_one) A B
  have hpm : 0 ≤ p * m := by positivity
  have h6 : 0 ≤ (A.card : ℝ) * (p * m) := by positivity
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- **Imbalanced pairs** of sets of good vertices satisfy the discrepancy bound. -/
theorem imbalanced {w : Fin m → Cube m → ℝ} (hw : ∀ i x, 0 ≤ w i x) {p γ η : ℝ}
    (hp : 0 ≤ p) (hγ1 : γ ≤ 1) (hη : 0 < η) {A B : Finset (Cube m)}
    (hA : Disjoint A (badSet w p γ)) (hB : Disjoint B (badSet w p γ)) (hbal : ¬ Bal η A B) :
    |cutW w A B - p * cutW 1 A B| ≤ η * p * m * Real.sqrt (A.card * B.card) := by
  have hpm : 0 ≤ p * m := by positivity
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 16 * a < η ^ 2 * b →
      3 * a ≤ η * Real.sqrt (a * b) := by
    intro a b ha hb hab
    have hsq := Real.sq_sqrt (mul_nonneg ha hb)
    have h1 : (η * Real.sqrt (a * b)) ^ 2 = η ^ 2 * (a * b) := by rw [mul_pow, hsq]
    have h2 : (3 * a) ^ 2 ≤ (η * Real.sqrt (a * b)) ^ 2 := by
      rw [h1]; nlinarith [mul_le_mul_of_nonneg_left hab.le ha]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h2
  simp only [Bal, not_and_or, not_le] at hbal
  rcases hbal with h | h
  · have := key _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) h
    calc _ ≤ 3 * p * m * A.card := abs_le_three hw hp hγ1 A B hA
      _ = p * m * (3 * A.card) := by ring
      _ ≤ p * m * (η * Real.sqrt (A.card * B.card)) := mul_le_mul_of_nonneg_left this hpm
      _ = _ := by ring
  · have := key _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) h
    rw [mul_comm (B.card : ℝ)] at this
    calc _ ≤ 3 * p * m * B.card := by
          rw [cutW_comm w, cutW_comm 1]; exact abs_le_three hw hp hγ1 B A hB
      _ = p * m * (3 * B.card) := by ring
      _ ≤ p * m * (η * Real.sqrt (A.card * B.card)) := mul_le_mul_of_nonneg_left this hpm
      _ = _ := by ring

/-- The number of hypercube edges between `A` and `B` is at most that inside `A ∪ B`. -/
theorem two_cutW_one_le (A B : Finset (Cube m)) : 2 * cutW 1 A B ≤ ein (A ∪ B) := by
  classical
  unfold cutW ein
  rw [sum_comm, mul_sum]
  refine sum_le_sum fun i _ ↦ ?_
  rw [← sum_lower, mul_sum]
  refine sum_le_sum fun x _ ↦ ?_
  simp only [flip_flip, Pi.one_apply, one_mul, mem_union]
  split_ifs <;> norm_num <;> tauto

/-- For balanced `A, B`: `|A| |B| ≥ η² (|A| + |B|)² / 64`. -/
theorem bal_sq {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) {A B : Finset (Cube m)}
    (h : Bal η A B) :
    η ^ 2 * ((A.card : ℝ) + B.card) ^ 2 ≤ 64 * (A.card * B.card) := by
  obtain ⟨h1, h2⟩ := h
  have ha : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hη2 : η ^ 2 ≤ 1 := by nlinarith [sq_nonneg η, sq_abs η]
  nlinarith [mul_le_mul_of_nonneg_left h1 hb, mul_le_mul_of_nonneg_left h2 ha, mul_nonneg ha hb]

theorem sqrt_ge_of_bal {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {A B : Finset (Cube m)}
    (h : Bal η A B) : η * ((A.card : ℝ) + B.card) / 8 ≤ Real.sqrt (A.card * B.card) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have := bal_sq hη.le hη1 h
  nlinarith

/-- **Small balanced pairs** satisfy the discrepancy bound, by edge isoperimetry. -/
theorem small {w : Fin m → Cube m → ℝ} (hw0 : ∀ i x, 0 ≤ w i x)
    (hw1 : ∀ i x, w i x ≤ 1)
    {p η : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hL : 16 * Real.log m ≤ η ^ 2 * p * m) {A B : Finset (Cube m)} (hAB : Disjoint A B)
    (hne : (A ∪ B).Nonempty) (hbal : Bal η A B) (hsmall : (A ∪ B).card ≤ m) :
    |cutW w A B - p * cutW 1 A B| ≤ η * p * m * Real.sqrt (A.card * B.card) := by
  classical
  have h1 := cutW_le_cutW_one hw1 A B
  have h4 := cutW_nonneg hw0 A B
  have h5 := cutW_nonneg (w := 1) (fun _ _ ↦ zero_le_one) A B
  have h6 := two_cutW_one_le A B
  have h7 := ein_le (A ∪ B)
  have hpos : (0 : ℝ) < (A ∪ B).card := by exact_mod_cast card_pos.2 hne
  have hlog : Real.log (A ∪ B).card ≤ Real.log m :=
    Real.log_le_log hpos (by exact_mod_cast hsmall)
  have hcard : ((A ∪ B).card : ℝ) = A.card + B.card := by
    rw [card_union_of_disjoint hAB]; push_cast; ring
  have h8 : |cutW w A B - p * cutW 1 A B| ≤ 2 * (A.card + B.card) * Real.log m := by
    rw [abs_le]
    rw [hcard] at h7 hpos hlog
    constructor <;> nlinarith
  have h9 := sqrt_ge_of_bal hη hη1 hbal
  have hpm : 0 ≤ p * m := by positivity
  calc _ ≤ 2 * (A.card + B.card) * Real.log m := h8
    _ ≤ p * m * (η * (η * ((A.card : ℝ) + B.card) / 8)) := by nlinarith
    _ ≤ p * m * (η * Real.sqrt (A.card * B.card)) := by gcongr
    _ = _ := by ring

/-- **Cauchy–Schwarz**: `√(ab) + √(cd) ≤ √((a + c)(b + d))`. -/
theorem sqrt_mul_add_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) :
    Real.sqrt (a * b) + Real.sqrt (c * d) ≤ Real.sqrt ((a + c) * (b + d)) := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul hc]
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have := Real.sq_sqrt ha
  have := Real.sq_sqrt hb
  have := Real.sq_sqrt hc
  have := Real.sq_sqrt hd
  nlinarith [sq_nonneg (Real.sqrt a * Real.sqrt d - Real.sqrt c * Real.sqrt b)]

/-- **The deterministic part of the proof**: if the bound holds for the large balanced pairs with
a connected union, it holds for all disjoint sets of good vertices. -/
theorem disc_of_cand {w : Fin m → Cube m → ℝ} (hw0 : ∀ i x, 0 ≤ w i x)
    (hw1 : ∀ i x, w i x ≤ 1)
    {p γ η : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hγ1 : γ ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hL : 16 * Real.log m ≤ η ^ 2 * p * m)
    (hcand : ∀ A B : Finset (Cube m), Cand η A B →
      |cutW w A B - p * cutW 1 A B| ≤ η * p * m * Real.sqrt (A.card * B.card)) :
    Disc w p γ η := by
  classical
  suffices h : ∀ n, ∀ S T : Finset (Cube m), (S ∪ T).card = n → Disjoint S T →
      Disjoint S (badSet w p γ) → Disjoint T (badSet w p γ) →
      |cutW w S T - p * cutW 1 S T| ≤ η * p * m * Real.sqrt (S.card * T.card) from
    fun S T h1 h2 h3 ↦ h _ S T rfl h1 h2 h3
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S T hn hST hS hT
  have hpm : 0 ≤ η * p * m := by positivity
  by_cases hc : Conn (S ∪ T)
  · rcases S.eq_empty_or_nonempty with rfl | hSne
    · simp only [cutW_empty_left, mul_zero, sub_self, abs_zero]; positivity
    rcases T.eq_empty_or_nonempty with rfl | hTne
    · simp only [cutW_empty_right, mul_zero, sub_self, abs_zero]; positivity
    by_cases hbal : Bal η S T
    · by_cases hsz : m ≤ (S ∪ T).card
      · exact hcand S T ⟨hST, hSne, hTne, hc, hbal, hsz⟩
      · exact small hw0 hw1 hp hp1 hη hη1 hL hST (hSne.mono subset_union_left) hbal (by omega)
    · exact imbalanced hw0 hp hγ1 hη hS hT hbal
  · simp only [Conn, not_forall, not_exists, not_and, exists_prop] at hc
    obtain ⟨V, hVsub, hVne, hVne', hV⟩ := hc
    have hsplit : ∀ x ∈ S ∪ T, ∀ i, flip x i ∈ S ∪ T → (x ∈ V ↔ flip x i ∈ V) := by
      intro x hx i hf
      constructor
      · intro hxV
        by_contra h
        exact hV x hxV i hf h
      · intro hfV
        by_contra h
        exact hV _ hfV i (by rwa [flip_flip]) (by rwa [flip_flip])
    rw [cutW_split w S T V hsplit, cutW_split 1 S T V hsplit]
    have e1 : (S ∩ V) ∪ (T ∩ V) = V := by
      rw [← union_inter_distrib_right]; exact inter_eq_right.2 hVsub
    have e2 : (S \ V) ∪ (T \ V) = (S ∪ T) \ V := (union_sdiff_distrib S T V).symm
    have hlt1 : V.card < n := by
      rw [← hn]; exact card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hVsub, hVne'⟩)
    have hlt2 : ((S ∪ T) \ V).card < n := by
      rw [← hn]; exact card_lt_card (sdiff_ssubset hVsub hVne)
    have h1 := ih _ hlt1 (S ∩ V) (T ∩ V) (by rw [e1]) (disjoint_of_subset_left inter_subset_left
      (disjoint_of_subset_right inter_subset_left hST))
      (disjoint_of_subset_left inter_subset_left hS) (disjoint_of_subset_left inter_subset_left hT)
    have h2 := ih _ hlt2 (S \ V) (T \ V) (by rw [e2]) (disjoint_of_subset_left sdiff_subset
      (disjoint_of_subset_right sdiff_subset hST))
      (disjoint_of_subset_left sdiff_subset hS) (disjoint_of_subset_left sdiff_subset hT)
    have hcS : (S.card : ℝ) = (S ∩ V).card + (S \ V).card := by
      rw [← card_inter_add_card_sdiff S V]; push_cast; ring
    have hcT : (T.card : ℝ) = (T ∩ V).card + (T \ V).card := by
      rw [← card_inter_add_card_sdiff T V]; push_cast; ring
    have hcs := sqrt_mul_add_le (Nat.cast_nonneg (S ∩ V).card) (Nat.cast_nonneg (T ∩ V).card)
      (Nat.cast_nonneg (S \ V).card) (Nat.cast_nonneg (T \ V).card)
    rw [← hcS, ← hcT] at hcs
    calc _ = |(cutW w (S ∩ V) (T ∩ V) - p * cutW 1 (S ∩ V) (T ∩ V)) +
          (cutW w (S \ V) (T \ V) - p * cutW 1 (S \ V) (T \ V))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = η * p * m * (Real.sqrt ((S ∩ V).card * (T ∩ V).card) +
          Real.sqrt ((S \ V).card * (T \ V).card)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcs hpm

/-! ### The probabilistic part -/

/-- The coins that decide the edges: `(i, x)` with `xᵢ = false`. -/
def idx : Finset (Fin m × Cube m) := univ.filter fun ix ↦ ix.2 ix.1 = false

open Classical in
/-- The indicator that the edge `{x, flip x i}` joins `A` and `B`. -/
noncomputable def coef (A B : Finset (Cube m)) (ix : Fin m × Cube m) : ℝ :=
  if (ix.2 ∈ A ∧ flip ix.2 ix.1 ∈ B) ∨ (ix.2 ∈ B ∧ flip ix.2 ix.1 ∈ A) then 1 else 0

theorem cutW_eq_sum (w : Fin m → Cube m → ℝ) (A B : Finset (Cube m)) :
    cutW w A B = ∑ ix ∈ idx, w ix.1 ix.2 * coef A B ix := by
  unfold cutW idx coef
  rw [sum_filter, Fintype.sum_prod_type]
  simp only [sum_filter]

theorem sum_coef_sq (A B : Finset (Cube m)) : ∑ ix ∈ idx, coef A B ix ^ 2 = cutW 1 A B := by
  rw [cutW_eq_sum]
  refine sum_congr rfl fun ix _ ↦ ?_
  unfold coef
  split_ifs <;> simp

theorem abs_coef_le (A B : Finset (Cube m)) (ix : Fin m × Cube m) : |coef A B ix| ≤ 1 := by
  unfold coef
  split_ifs <;> simp

theorem bit_nonneg' (b : Bool) : 0 ≤ bit b := by cases b <;> simp [bit]

theorem bit_le_one' (b : Bool) : bit b ≤ 1 := by cases b <;> simp [bit]

/-- The discrepancy of `(A, B)` as a linear form in the centred coins. -/
theorem disc_eq_sum {Ω : Type*} (a : Fin m × Cube m → Ω → Bool) (ω : Ω) (p : ℝ)
    (A B : Finset (Cube m)) :
    cutW (coinW a ω) A B - p * cutW 1 A B =
      ∑ ix ∈ idx, coef A B ix * (bit (a ix ω) - p) := by
  rw [cutW_eq_sum, cutW_eq_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun ix _ ↦ ?_
  simp only [coinW, Pi.one_apply]
  ring

/-- The exponent in Bernstein's inequality for a large balanced pair. -/
theorem exponent_le {η P L a b h q pp k : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hP : 0 < P)
    (hL : 0 ≤ L) (hk : 0 ≤ k) (hPL : 2048 * k * L ≤ η ^ 4 * P) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 0 < q)
    (hqs : q ≤ a + b) (hbal : η ^ 2 * (a + b) ^ 2 ≤ 64 * q ^ 2) (hh0 : 0 ≤ pp * h)
    (hh : pp * h ≤ P * (a + b)) :
    -(η * P * q) ^ 2 / (2 * (pp * h + 1 * (η * P * q) / 3)) ≤ -(12 * k * (a + b) * L) := by
  have hηq : η * q ≤ a + b := by nlinarith
  have hD : 0 < 2 * (pp * h + 1 * (η * P * q) / 3) := by positivity
  rw [neg_div, neg_le_neg_iff, le_div_iff₀ hD]
  have f1 : 2 * (pp * h + 1 * (η * P * q) / 3) ≤ 8 / 3 * (P * (a + b)) := by
    have : η * P * q ≤ P * (a + b) := by nlinarith
    linarith
  have f2 : 12 * k * (a + b) * L * (2 * (pp * h + 1 * (η * P * q) / 3)) ≤
      12 * k * (a + b) * L * (8 / 3 * (P * (a + b))) :=
    mul_le_mul_of_nonneg_left f1 (by positivity)
  have f3 : η ^ 2 * P ^ 2 * (η ^ 2 * (a + b) ^ 2) ≤ η ^ 2 * P ^ 2 * (64 * q ^ 2) :=
    mul_le_mul_of_nonneg_left hbal (by positivity)
  have f4 : 2048 * k * L * (P * (a + b) ^ 2) ≤ η ^ 4 * P * (P * (a + b) ^ 2) :=
    mul_le_mul_of_nonneg_right hPL (by positivity)
  nlinarith

theorem exp_neg_eq_pow {m : ℕ} (hm : 0 < m) (k s : ℕ) :
    Real.exp (-(12 * (k : ℝ) * (s : ℝ) * Real.log m)) = ((m : ℝ)⁻¹) ^ (12 * k * s) := by
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (m : ℝ)⁻¹), ← Real.exp_nat_mul,
    Real.log_inv]
  congr 1
  push_cast
  ring

open MeasureTheory in
/-- **Bernstein's inequality for a large balanced pair**: the bound fails with probability at most
`2 m^(-12 k |A ∪ B|)` when `p m ≥ 2048 k log m / η⁴`. -/
theorem prob_bad {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Fin m × Cube m → Ω → Bool} {p η : ℝ} (h : IsCoins μ a p) (hm : 2 ≤ m)
    (hη : 0 < η) (hη1 : η ≤ 1) (hp : 0 < p) {k : ℕ}
    (hpm : 2048 * k * Real.log m ≤ η ^ 4 * (p * m)) {A B : Finset (Cube m)} (hAB : Cand η A B) :
    μ.real {ω | η * p * m * Real.sqrt (A.card * B.card) ≤
        |cutW (coinW a ω) A B - p * cutW 1 A B|} ≤
      2 * ((m : ℝ)⁻¹) ^ (12 * k * (A ∪ B).card) := by
  classical
  obtain ⟨hdisj, hA, hB, -, hbal, -⟩ := hAB
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlog : 0 < Real.log m := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  simp_rw [disc_eq_sum a _ p A B]
  have ha : (0 : ℝ) < A.card := by exact_mod_cast card_pos.2 hA
  have hb : (0 : ℝ) < B.card := by exact_mod_cast card_pos.2 hB
  have hq : 0 < Real.sqrt (A.card * B.card) := Real.sqrt_pos.2 (by positivity)
  have ht : 0 ≤ η * p * m * Real.sqrt (A.card * B.card) := by positivity
  refine (h.measureReal_abs_sum_ge_le idx (coef A B) (fun ix _ ↦ abs_coef_le A B ix) ht).trans ?_
  rw [← exp_neg_eq_pow (by omega), card_union_of_disjoint hdisj]
  gcongr
  rw [sum_coef_sq]
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ A.card * B.card by positivity)
  have hqs : Real.sqrt (A.card * B.card) ≤ A.card + B.card := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hbal' := bal_sq hη.le hη1 hbal
  rw [← hsq] at hbal'
  have hh := cutW_le_sum_deg (w := 1) (fun _ _ ↦ zero_le_one) A B
  simp only [deg_one, sum_const, nsmul_eq_mul] at hh
  have hh0 := cutW_nonneg (w := 1) (fun _ _ ↦ zero_le_one) A B
  have := exponent_le (P := p * m) (L := Real.log m) (a := A.card) (b := B.card)
    (pp := p) (h := cutW 1 A B) (k := k) hη hη1 (by positivity) hlog.le (Nat.cast_nonneg k) hpm
    ha.le hb.le hq hqs hbal'
    (by positivity) (by
      have h1 := mul_le_mul_of_nonneg_left hh hp.le
      have h2 := mul_pos (mul_pos hp hm0) hb
      linarith)
  push_cast
  convert this using 3 <;> ring

/-! ### The union bound -/

open Classical in
/-- The pairs of the union bound. -/
noncomputable def cands (η : ℝ) : Finset (Finset (Cube m) × Finset (Cube m)) :=
  univ.filter fun AB ↦ Cand η AB.1 AB.2

/-- **Counting connected sets**: at most `2^m m^(2(t-1)) 2^t` pairs of the union bound have a
union of size `t` (a connected set is the vertex set of a walk of length `2 (t - 1)`). -/
theorem card_cands_le (η : ℝ) (t : ℕ) :
    ((cands (m := m) η).filter fun AB ↦ (AB.1 ∪ AB.2).card = t).card ≤
      2 ^ m * m ^ (2 * (t - 1)) * 2 ^ t := by
  classical
  set Wt : Finset (Finset (Cube m)) :=
    ((univ : Finset (Cube m × List.Vector (Fin m) (2 * (t - 1)))).image
      fun xv ↦ wset xv.1 xv.2.toList).filter (·.card = t) with hWt
  have hsub : (cands (m := m) η).filter (fun AB ↦ (AB.1 ∪ AB.2).card = t) ⊆
      Wt.biUnion fun W ↦ W.powerset.image fun A ↦ (A, W \ A) := by
    rintro ⟨A, B⟩ hAB
    simp only [cands, mem_filter, mem_univ, true_and] at hAB
    obtain ⟨⟨hdisj, hA, -, hconn, -, -⟩, ht⟩ := hAB
    obtain ⟨x, l, hlen, hW⟩ := exists_walk hconn (hA.mono subset_union_left)
    rw [ht] at hlen
    simp only [mem_biUnion, mem_image, mem_powerset, hWt, mem_filter, mem_univ, true_and]
    refine ⟨A ∪ B, ⟨⟨(x, ⟨l, hlen⟩), hW⟩, ht⟩, A, subset_union_left, ?_⟩
    rw [union_sdiff_cancel_left hdisj]
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  have h1 : ∀ W ∈ Wt, (W.powerset.image fun A ↦ (A, W \ A)).card ≤ 2 ^ t := by
    intro W hW
    rw [hWt, mem_filter] at hW
    refine card_image_le.trans ?_
    rw [card_powerset, hW.2]
  refine (sum_le_card_nsmul _ _ _ h1).trans ?_
  rw [smul_eq_mul]
  gcongr
  refine (card_filter_le _ _).trans (card_image_le.trans ?_)
  simp [card_vector]

/-- The numerical sum of the union bound. -/
theorem final_sum (q : ℕ) (hm : 2 ≤ m) :
    ∑ t ∈ Ico m (2 ^ m + 1), ((2 : ℝ) ^ m * (m : ℝ) ^ (2 * (t - 1)) * 2 ^ t) *
      (2 * ((m : ℝ)⁻¹) ^ (12 * (q + 1) * t)) ≤ ((m : ℝ)⁻¹) ^ q := by
  set r : ℝ := (m : ℝ)⁻¹ with hr
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hr0 : 0 < r := by positivity
  have hr2 : r ≤ 1 / 2 := by
    rw [hr, one_div]; exact inv_anti₀ (by norm_num) hm'
  have hmr : (m : ℝ) * r = 1 := mul_inv_cancel₀ (by positivity)
  have hr1 : r ≤ 1 := by linarith
  set e : ℕ := 12 * q + 9 with he
  have hterm : ∀ t ∈ Ico m (2 ^ m + 1), ((2 : ℝ) ^ m * (m : ℝ) ^ (2 * (t - 1)) * 2 ^ t) *
      (2 * r ^ (12 * (q + 1) * t)) ≤ 2 * 2 ^ m * (r ^ e) ^ m := by
    intro t ht
    have hmt : m ≤ t := (mem_Ico.1 ht).1
    have e1 : (m : ℝ) ^ (2 * (t - 1)) ≤ (m : ℝ) ^ (2 * t) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have e2 : (m : ℝ) ^ (2 * t) * r ^ (12 * (q + 1) * t) = (r ^ (e + 1)) ^ t := by
      rw [show 12 * (q + 1) * t = 2 * t + (e + 1) * t by rw [he]; ring, pow_add, ← mul_assoc,
        ← mul_pow, hmr, one_pow, one_mul, pow_mul]
    have e3 : (2 : ℝ) ^ t * (r ^ (e + 1)) ^ t ≤ (r ^ e) ^ t := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      calc 2 * r ^ (e + 1) = (2 * r) * r ^ e := by ring
        _ ≤ 1 * r ^ e := by gcongr; linarith
        _ = r ^ e := one_mul _
    have e4 : (r ^ e) ^ t ≤ (r ^ e) ^ m :=
      pow_le_pow_of_le_one (by positivity) (pow_le_one₀ hr0.le hr1) hmt
    calc ((2 : ℝ) ^ m * (m : ℝ) ^ (2 * (t - 1)) * 2 ^ t) * (2 * r ^ (12 * (q + 1) * t))
        ≤ ((2 : ℝ) ^ m * (m : ℝ) ^ (2 * t) * 2 ^ t) * (2 * r ^ (12 * (q + 1) * t)) := by
          gcongr
      _ = 2 * 2 ^ m * (2 ^ t * ((m : ℝ) ^ (2 * t) * r ^ (12 * (q + 1) * t))) := by ring
      _ = 2 * 2 ^ m * (2 ^ t * (r ^ (e + 1)) ^ t) := by rw [e2]
      _ ≤ 2 * 2 ^ m * (r ^ e) ^ t := by gcongr
      _ ≤ 2 * 2 ^ m * (r ^ e) ^ m := by gcongr
  refine (sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [Nat.card_Ico, nsmul_eq_mul]
  have hc : ((2 ^ m + 1 - m : ℕ) : ℝ) ≤ 2 * 2 ^ m := by
    have : (2 ^ m + 1 - m : ℕ) ≤ 2 * 2 ^ m := by
      have := Nat.one_le_two_pow (n := m); omega
    exact_mod_cast this
  have e5 : (2 * 2 ^ m) * (2 * 2 ^ m * (r ^ e) ^ m) =
      4 * ((4 * r ^ 2) ^ m * r ^ ((e - 2) * m)) := by
    have h4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
    rw [mul_pow, h4, ← pow_mul, ← pow_mul, show e * m = 2 * m + (e - 2) * m by
      rw [← add_mul]; congr 1; omega, pow_add]
    ring
  have e6 : (4 * r ^ 2) ^ m ≤ 1 := pow_le_one₀ (by positivity) (by nlinarith)
  have e7 : r ^ ((e - 2) * m) ≤ r ^ (q + 2) :=
    pow_le_pow_of_le_one hr0.le hr1 (by
      rw [show e - 2 = 12 * q + 7 by omega]
      nlinarith)
  have e8 : 4 * r ^ (q + 2) ≤ r ^ q := by
    have : r ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ hr0.le hr2 2
    have h3 : 0 < r ^ q := by positivity
    calc 4 * r ^ (q + 2) = (4 * r ^ 2) * r ^ q := by ring
      _ ≤ 1 * r ^ q := by gcongr; norm_num at this; linarith
      _ = r ^ q := one_mul _
  calc ((2 ^ m + 1 - m : ℕ) : ℝ) * (2 * 2 ^ m * (r ^ e) ^ m)
      ≤ (2 * 2 ^ m) * (2 * 2 ^ m * (r ^ e) ^ m) := by gcongr
    _ = 4 * ((4 * r ^ 2) ^ m * r ^ ((e - 2) * m)) := e5
    _ ≤ 4 * (1 * r ^ (q + 2)) := by gcongr
    _ ≤ r ^ q := by linarith

/-- The sum of the failure probabilities of the union bound is at most `1 / m^q`. -/
theorem sum_cands_le (η : ℝ) (q : ℕ) (hm : 2 ≤ m) :
    ∑ AB ∈ cands (m := m) η, 2 * ((m : ℝ)⁻¹) ^ (12 * (q + 1) * (AB.1 ∪ AB.2).card) ≤
      ((m : ℝ)⁻¹) ^ q := by
  classical
  have hmaps : ∀ AB ∈ cands (m := m) η, (AB.1 ∪ AB.2).card ∈ Ico m (2 ^ m + 1) := by
    intro AB hAB
    simp only [cands, mem_filter, mem_univ, true_and] at hAB
    rw [mem_Ico]
    refine ⟨hAB.2.2.2.2.2, Nat.lt_succ_of_le ?_⟩
    calc (AB.1 ∪ AB.2).card ≤ (univ : Finset (Cube m)).card := card_le_univ _
      _ = 2 ^ m := by simp
  rw [← sum_fiberwise_of_maps_to hmaps]
  calc ∑ t ∈ Ico m (2 ^ m + 1),
        ∑ AB ∈ (cands η).filter (fun AB ↦ (AB.1 ∪ AB.2).card = t),
        2 * ((m : ℝ)⁻¹) ^ (12 * (q + 1) * (AB.1 ∪ AB.2).card)
      = ∑ t ∈ Ico m (2 ^ m + 1),
          (((cands (m := m) η).filter (fun AB ↦ (AB.1 ∪ AB.2).card = t)).card : ℝ) *
            (2 * ((m : ℝ)⁻¹) ^ (12 * (q + 1) * t)) := by
        refine sum_congr rfl fun t _ ↦ ?_
        rw [sum_congr rfl (g := fun _ ↦ 2 * ((m : ℝ)⁻¹) ^ (12 * (q + 1) * t))
          (fun AB hAB ↦ by rw [(mem_filter.1 hAB).2]), sum_const, nsmul_eq_mul]
    _ ≤ ∑ t ∈ Ico m (2 ^ m + 1), ((2 : ℝ) ^ m * (m : ℝ) ^ (2 * (t - 1)) * 2 ^ t) *
          (2 * ((m : ℝ)⁻¹) ^ (12 * (q + 1) * t)) := by
        gcongr with t ht
        exact_mod_cast card_cands_le η t
    _ ≤ _ := final_sum q hm

end Disc

open MeasureTheory

/-- **Discrepancy between sets of good vertices**, with failure probability at most `1/m^q` for any
`q`. -/
theorem disc_whp_pow {γ η : ℝ} (hγ1 : γ ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ p : ℝ, C * Real.log m / m ≤ p → p ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Fin m × Cube m → Ω → Bool),
        IsCoins μ a p →
        1 - 1 / (m : ℝ) ^ q ≤ μ.real {ω | Disc (coinW a ω) p γ η} := by
  refine ⟨2048 * (q + 1) / η ^ 4, by positivity, 2, fun m hm p hp hp1 Ω _ μ a h ↦ ?_⟩
  classical
  have := h.isProb
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlog : 0 < Real.log m := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hpm : 2048 * ((q + 1 : ℕ) : ℝ) * Real.log m ≤ η ^ 4 * (p * m) := by
    have h1 := (div_le_iff₀ hm0).1 hp
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h1
    push_cast
    linarith
  have hq1 : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  have hp0 : 0 < p := by
    by_contra hneg
    push Not at hneg
    have : η ^ 4 * (p * m) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonpos_of_nonneg hneg hm0.le)
    have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2048) hq1) hlog
    linarith
  have hL16 : 16 * Real.log m ≤ η ^ 2 * p * m := by
    have hη2 : η ^ 4 ≤ η ^ 2 := pow_le_pow_of_le_one hη.le hη1 (by norm_num)
    have : η ^ 4 * (p * m) ≤ η ^ 2 * (p * m) := mul_le_mul_of_nonneg_right hη2 (by positivity)
    have h1 : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos q
    nlinarith
  set G := {ω | Disc (coinW a ω) p γ η} with hG
  set bad : Finset (Cube m) × Finset (Cube m) → Set Ω := fun AB ↦
    {ω | η * p * m * Real.sqrt (AB.1.card * AB.2.card) ≤
      |cutW (coinW a ω) AB.1 AB.2 - p * cutW 1 AB.1 AB.2|} with hbad
  have hsub : Gᶜ ⊆ ⋃ AB ∈ Disc.cands (m := m) η, bad AB := by
    intro ω hω
    simp only [Set.mem_iUnion, exists_prop, hbad, Set.mem_ofPred_eq]
    by_contra hc
    push Not at hc
    apply hω
    exact Disc.disc_of_cand (fun _ _ ↦ Disc.bit_nonneg' _) (fun _ _ ↦ Disc.bit_le_one' _)
      hp0.le hp1 hγ1 hη hη1 hL16
      fun A B hAB ↦ (hc (A, B) (by simpa [Disc.cands] using hAB)).le
  have h1 : μ.real Gᶜ ≤ μ.real (⋃ AB ∈ Disc.cands (m := m) η, bad AB) :=
    measureReal_mono hsub (measure_ne_top μ _)
  have h2 := measureReal_biUnion_finset_le (μ := μ) (Disc.cands (m := m) η) bad
  have h3 : ∑ AB ∈ Disc.cands (m := m) η, μ.real (bad AB) ≤
      ∑ AB ∈ Disc.cands (m := m) η, 2 * ((m : ℝ)⁻¹) ^ (12 * (q + 1) * (AB.1 ∪ AB.2).card) :=
    sum_le_sum fun AB hAB ↦ Disc.prob_bad h hm hη hη1 hp0 hpm
      (by simpa [Disc.cands] using hAB)
  have h4 := Disc.sum_cands_le (m := m) η q hm
  have h5 : 1 ≤ μ.real G + μ.real Gᶜ := by
    have := measureReal_union_le (μ := μ) G Gᶜ
    rwa [Set.union_compl_self, probReal_univ] at this
  rw [one_div, ← inv_pow]
  linarith

/-- **Discrepancy between sets of good vertices** ([BMW26, Lemma 5.3]). -/
theorem disc_whp {γ η : ℝ} (_hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ p : ℝ, C * Real.log m / m ≤ p → p ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Fin m × Cube m → Ω → Bool),
        IsCoins μ a p →
        1 - 1 / (m : ℝ) ^ 3 ≤ μ.real {ω | Disc (coinW a ω) p γ η} := by
  obtain ⟨C, hC, m₀, h⟩ := disc_whp_pow hγ1 hη hη1 3
  exact ⟨C, hC, m₀, fun m hm p hp hp1 _ _ μ a ha ↦ by exact_mod_cast h m hm p hp hp1 μ a ha⟩

end BMW26
