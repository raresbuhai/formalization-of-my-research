module

public import Background.RandomGraph
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Pruning

Shared by the papers (first written for [BKS23], used by [BBKS24]).

[BKS23, `lem:clique-intersection`, `lem:sets-pinex`, and the pruning of the proof of Theorem 5.6]:
from a list of candidate sets that contains the planted clique `S*`, keep the `k`-cliques of the
input graph `G`, then prune greedily: keep a set if it meets every set kept before it in fewer
than `Δ` vertices (`Pruning.cleanup`).

* `Pruning.mem_cleanup`: `S*` survives if every other `k`-clique of `G` meets it in fewer
  than `Δ` vertices. In `FK(n, k, p)` this holds with `Δ = ℓ₀` when the cut of the random graph
  has no large bicliques (`Pruning.card_inter_lt`, from `BKS23.RandomGraph.NoBiclique`).
* `Pruning.length_cleanup_le`: the output has at most `(n/k)(1 + 2nΔ/k²)` sets when
  `2nΔ ≤ k²`, by Corrádi's lemma (`Pruning.card_mul_le_corradi`).

**The number of sets** (`lem:sets-pinex`) is bounded by Corrádi's lemma: with `dₓ` the number of
sets containing `x`, Cauchy–Schwarz on `∑ₓ dₓ = mk` and `∑ₓ dₓ² = ∑_{S,T} |S ∩ T| ≤ mk + m(m-1)Δ`
gives `m (k² - nΔ) ≤ n (k - Δ)` for every `m`.
-/

@[expose] public section

namespace Pruning

open Finset

/-! ### Greedy pruning -/

section Prune

variable {α : Type*} (ok : α → α → Bool)

/-- Greedy pruning with the kept elements `kept`: keep each element of the list that is
compatible (`ok y x`) with every element kept before it. -/
def pruneAux : List α → List α → List α
  | kept, [] => kept
  | kept, x :: xs => pruneAux (if kept.all (ok · x) then kept ++ [x] else kept) xs

/-- Greedy pruning. -/
def prune (l : List α) : List α := pruneAux ok [] l

variable {ok}

theorem mem_pruneAux_of_mem {kept l : List α} {x : α} (h : x ∈ kept) :
    x ∈ pruneAux ok kept l := by
  induction l generalizing kept with
  | nil => exact h
  | cons z zs ih =>
    rw [pruneAux]
    split_ifs
    · exact ih (List.mem_append_left _ h)
    · exact ih h

theorem mem_of_mem_pruneAux {kept l : List α} {x : α} (h : x ∈ pruneAux ok kept l) :
    x ∈ kept ∨ x ∈ l := by
  induction l generalizing kept with
  | nil => exact Or.inl h
  | cons z zs ih =>
    rw [pruneAux] at h
    split_ifs at h
    · rcases ih h with h | h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp_all)
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases ih h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem pairwise_pruneAux {kept l : List α} (h : kept.Pairwise fun y x ↦ ok y x) :
    (pruneAux ok kept l).Pairwise fun y x ↦ ok y x := by
  induction l generalizing kept with
  | nil => exact h
  | cons z zs ih =>
    rw [pruneAux]
    split_ifs with hz
    · refine ih (List.pairwise_append.2 ⟨h, by simp, fun y hy x hx ↦ ?_⟩)
      rw [List.mem_singleton] at hx
      subst hx
      exact List.all_eq_true.1 hz y hy
    · exact ih h

/-- An element compatible with every other element of the list is kept. -/
theorem mem_pruneAux {kept l : List α} {x : α} (hx : x ∈ l)
    (hok : ∀ y ∈ kept ++ l, y ≠ x → ok y x) : x ∈ pruneAux ok kept l := by
  induction l generalizing kept with
  | nil => simp at hx
  | cons z zs ih =>
    rw [pruneAux]
    by_cases hzx : z = x
    · subst hzx
      split_ifs with hall
      · exact mem_pruneAux_of_mem (List.mem_append_right _ (List.mem_singleton_self _))
      · rw [List.all_eq_true] at hall
        simp only [not_forall, exists_prop] at hall
        obtain ⟨y, hy, hny⟩ := hall
        by_cases hyz : y = z
        · subst hyz
          exact mem_pruneAux_of_mem hy
        · exact absurd (hok y (List.mem_append_left _ hy) hyz) hny
    · have hxs : x ∈ zs := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm hzx
        · exact h
      refine ih hxs fun y hy hyx ↦ hok y ?_ hyx
      split_ifs at hy
      · rcases List.mem_append.1 hy with h | h
        · rcases List.mem_append.1 h with h | h
          · exact List.mem_append_left _ h
          · rw [List.mem_singleton] at h
            subst h
            exact List.mem_append_right _ List.mem_cons_self
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      · rcases List.mem_append.1 hy with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

theorem mem_prune {l : List α} {x : α} (hx : x ∈ l) (hok : ∀ y ∈ l, y ≠ x → ok y x) :
    x ∈ prune ok l :=
  mem_pruneAux hx (by simpa using hok)

theorem mem_of_mem_prune {l : List α} {x : α} (h : x ∈ prune ok l) : x ∈ l := by
  rcases mem_of_mem_pruneAux h with h | h
  · simp at h
  · exact h

theorem pairwise_prune (l : List α) : (prune ok l).Pairwise fun y x ↦ ok y x :=
  pairwise_pruneAux List.Pairwise.nil

omit ok in
/-- Pruning commutes with a map that respects the tests. -/
theorem pruneAux_map {β : Type*} (f : β → α) (ok : α → α → Bool) (ok' : β → β → Bool) :
    ∀ (kept l : List β), (∀ y ∈ kept ++ l, ∀ x ∈ kept ++ l, ok' y x = ok (f y) (f x)) →
      pruneAux ok (kept.map f) (l.map f) = (pruneAux ok' kept l).map f
  | kept, [], _ => by simp [pruneAux]
  | kept, x :: xs, h => by
    have hall : (kept.map f).all (ok · (f x)) = kept.all (ok' · x) := by
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact forall₂_congr fun y hy ↦ by rw [h y (by simp [hy]) x (by simp)]
    have hstep : (if (kept.map f).all (ok · (f x)) then kept.map f ++ [f x] else kept.map f) =
        (if kept.all (ok' · x) then kept ++ [x] else kept).map f := by
      rw [hall]
      split_ifs <;> simp
    rw [List.map_cons, pruneAux, pruneAux, hstep]
    refine pruneAux_map f ok ok' _ xs fun y hy z hz ↦ h y ?_ z ?_
    · split_ifs at hy <;> simp only [List.mem_append, List.mem_cons] at hy ⊢ <;>
        tauto
    · split_ifs at hz <;> simp only [List.mem_append, List.mem_cons] at hz ⊢ <;>
        tauto

end Prune

/-! ### Corrádi's lemma -/

/-- **Corrádi's lemma**: `m` sets of size `k` in an `n`-set, pairwise meeting in at most
`Δ ≤ k` elements, have `m (k² - nΔ) ≤ n (k - Δ)`. -/
theorem card_mul_le_corradi {n k Δ : ℕ} (hΔk : Δ ≤ k) (𝓕 : Finset (Finset (Fin n)))
    (hk : ∀ S ∈ 𝓕, S.card = k)
    (hΔ : ∀ S ∈ 𝓕, ∀ T ∈ 𝓕, S ≠ T → (S ∩ T).card ≤ Δ) :
    (𝓕.card : ℝ) * ((k : ℝ) ^ 2 - n * Δ) ≤ n * ((k : ℝ) - Δ) := by
  classical
  set m := (𝓕.card : ℝ)
  set d : Fin n → ℝ := fun x ↦ ∑ S ∈ 𝓕, if x ∈ S then (1 : ℝ) else 0
  have hcard : ∀ S : Finset (Fin n), ∑ x, (if x ∈ S then (1 : ℝ) else 0) = S.card := by
    intro S
    rw [sum_boole, filter_mem_eq_inter, univ_inter]
  have h1 : ∑ x, d x = m * k := by
    simp only [d]
    rw [sum_comm, sum_congr rfl fun S hS ↦ by rw [hcard, hk S hS], sum_const, nsmul_eq_mul]
  have hinter : ∀ S T : Finset (Fin n),
      ∑ x, (if x ∈ S then (1 : ℝ) else 0) * (if x ∈ T then 1 else 0) = (S ∩ T).card := by
    intro S T
    rw [← hcard]
    exact sum_congr rfl fun x _ ↦ by simp only [mem_inter]; split_ifs <;> simp_all
  have h2 : ∑ x, d x ^ 2 ≤ m * k + m * (m - 1) * Δ := by
    have : ∑ x, d x ^ 2 = ∑ S ∈ 𝓕, ∑ T ∈ 𝓕, ((S ∩ T).card : ℝ) := by
      simp only [d, sq, sum_mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun S _ ↦ ?_
      rw [sum_comm]
      exact sum_congr rfl fun T _ ↦ hinter S T
    rw [this]
    calc ∑ S ∈ 𝓕, ∑ T ∈ 𝓕, ((S ∩ T).card : ℝ) ≤ ∑ _S ∈ 𝓕, ((k : ℝ) + (m - 1) * Δ) := by
          refine sum_le_sum fun S hS ↦ ?_
          rw [← add_sum_erase 𝓕 _ hS, inter_self, hk S hS]
          refine add_le_add le_rfl ?_
          calc ∑ T ∈ 𝓕.erase S, ((S ∩ T).card : ℝ) ≤ ∑ _T ∈ 𝓕.erase S, (Δ : ℝ) :=
                sum_le_sum fun T hT ↦ by
                  exact_mod_cast hΔ S hS T (mem_of_mem_erase hT) (ne_of_mem_erase hT).symm
            _ = (m - 1) * Δ := by
                rw [sum_const, card_erase_of_mem hS, nsmul_eq_mul, Nat.cast_sub
                  (card_pos.2 ⟨S, hS⟩)]
                simp [m]
      _ = m * k + m * (m - 1) * Δ := by rw [sum_const, nsmul_eq_mul]; ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := univ) (f := d)
  simp only [card_univ, Fintype.card_fin] at hcs
  rw [h1] at hcs
  have hΔk' : (Δ : ℝ) ≤ k := by exact_mod_cast hΔk
  rcases (Nat.cast_nonneg 𝓕.card : (0 : ℝ) ≤ m).eq_or_lt with hm | hm
  · have hm0 : m = 0 := hm.symm
    rw [hm0, zero_mul]
    exact mul_nonneg (Nat.cast_nonneg n) (by linarith)
  · -- `m² k² ≤ n (m k + m (m - 1) Δ)`; divide by `m`.
    have h3 := hcs.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n))
    have h4 : m * (m * ((k : ℝ) ^ 2 - n * Δ)) ≤ m * (n * ((k : ℝ) - Δ)) := by nlinarith
    exact le_of_mul_le_mul_left h4 hm

/-- **The list size** [BKS23, `lem:sets-pinex`]: such a family has at most
`(n/k)(1 + 2nΔ/k²)` sets when `2nΔ ≤ k²`. -/
theorem card_le_of_inter_le {n k Δ : ℕ} (hk : 0 < k) (hΔk : Δ ≤ k) (h2 : 2 * n * Δ ≤ k ^ 2)
    (𝓕 : Finset (Finset (Fin n))) (hcard : ∀ S ∈ 𝓕, S.card = k)
    (hΔ : ∀ S ∈ 𝓕, ∀ T ∈ 𝓕, S ≠ T → (S ∩ T).card ≤ Δ) :
    (𝓕.card : ℝ) ≤ n / k * (1 + 2 * n * Δ / (k : ℝ) ^ 2) := by
  have h := card_mul_le_corradi hΔk 𝓕 hcard hΔ
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h2' : 2 * (n : ℝ) * Δ ≤ (k : ℝ) ^ 2 := by exact_mod_cast h2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hΔ0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg Δ
  have hpos : 0 < (k : ℝ) ^ 2 - n * Δ := by nlinarith
  -- `n (k - Δ) ≤ n k ≤ (n/k)(1 + 2nΔ/k²)(k² - nΔ)`.
  have hR : (n : ℝ) * ((k : ℝ) - Δ) ≤
      n / k * (1 + 2 * n * Δ / (k : ℝ) ^ 2) * ((k : ℝ) ^ 2 - n * Δ) := by
    have hx : (n : ℝ) / k * (1 + 2 * n * Δ / (k : ℝ) ^ 2) * ((k : ℝ) ^ 2 - n * Δ) =
        n * k + n / k * (n * Δ) * (1 - 2 * n * Δ / (k : ℝ) ^ 2) := by
      field_simp
      ring
    rw [hx]
    have h3 : 0 ≤ 1 - 2 * n * Δ / (k : ℝ) ^ 2 := by
      rw [sub_nonneg, div_le_one (by positivity)]
      exact h2'
    have h4 : 0 ≤ (n : ℝ) / k * (n * Δ) * (1 - 2 * n * Δ / (k : ℝ) ^ 2) := by positivity
    nlinarith
  exact le_of_mul_le_mul_right (h.trans hR) hpos

/-! ### Cliques meeting the planted clique -/

/-- **`lem:clique-intersection`, deterministically.** If the cut of `R` at `U` has no biclique
with `ℓ₀` vertices in `U` (`RandomGraph.NoBiclique`), and the cut of `G` is contained in that of
`R`, then every `k`-clique of `G` other than `U` (`|U| = k`) meets `U` in fewer than `ℓ₀`
vertices: its parts inside and outside `U` would form such a biclique. -/
theorem card_inter_lt {n k ℓ₀ : ℕ} {U : Finset (Fin n)} (hU : U.card = k)
    {R G : SimpleGraph (Fin n)} (hR : RandomGraph.NoBiclique U ℓ₀ R)
    (hcut : ∀ u ∈ U, ∀ v ∉ U, G.Adj u v → R.Adj u v) {S : Finset (Fin n)}
    (hS : G.IsNClique k S) (hne : S ≠ U) : (S ∩ U).card < ℓ₀ := by
  by_contra hle
  rw [not_lt] at hle
  have hB : (S \ U).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    exact hne (eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.1 h)
      (by rw [hU, hS.card_eq]))
  obtain ⟨a, ha, b, hb, hab⟩ := hR (S ∩ U) inter_subset_right (S \ U)
    (fun x hx ↦ mem_compl.2 (mem_sdiff.1 hx).2) hle hB
    (by rw [card_inter_add_card_sdiff, hS.card_eq, hU])
  have haU := (mem_inter.1 ha).2
  have hbU := (mem_sdiff.1 hb).2
  have hne' : a ≠ b := fun h ↦ hbU (h ▸ haU)
  exact hab (hcut a haU b hbU (hS.isClique (mem_inter.1 ha).1 (mem_sdiff.1 hb).1 hne'))

/-! ### The cleanup -/

open Classical in
/-- **The cleanup**: keep the candidates that are `k`-cliques of `G`, then prune greedily with
threshold `Δ` (keep a set if it meets every set kept before it in fewer than `Δ` vertices). -/
noncomputable def cleanup {n : ℕ} (G : SimpleGraph (Fin n)) (k Δ : ℕ)
    (C : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  prune (fun y x ↦ decide ((y ∩ x).card < Δ)) (C.filter fun S ↦ decide (G.IsNClique k S))

variable {n : ℕ} {G : SimpleGraph (Fin n)} {k Δ : ℕ} {C : List (Finset (Fin n))}

/-- The output consists of `k`-cliques of `G`. -/
theorem isNClique_of_mem_cleanup {S : Finset (Fin n)} (h : S ∈ cleanup G k Δ C) :
    G.IsNClique k S := by
  classical
  have := List.mem_filter.1 (mem_of_mem_prune h)
  simpa using this.2

/-- **The planted clique survives** if it is a candidate and every other `k`-clique of `G`
meets it in fewer than `Δ` vertices. -/
theorem mem_cleanup {U : Finset (Fin n)} (hU : U ∈ C) (hUc : G.IsNClique k U)
    (hother : ∀ S, G.IsNClique k S → S ≠ U → (S ∩ U).card < Δ) : U ∈ cleanup G k Δ C := by
  classical
  refine mem_prune (List.mem_filter.2 ⟨hU, by simpa using hUc⟩) fun S hS hne ↦ ?_
  have := (List.mem_filter.1 hS).2
  simpa using hother S (by simpa using this) hne

/-- **The list size** [BKS23, `lem:sets-pinex`]: at most `(n/k)(1 + 2nΔ/k²)` sets, when
`2nΔ ≤ k²` and `Δ ≤ k`. -/
theorem length_cleanup_le (hk : 0 < k) (hΔk : Δ ≤ k) (h2 : 2 * n * Δ ≤ k ^ 2) :
    ((cleanup G k Δ C).length : ℝ) ≤ n / k * (1 + 2 * n * Δ / (k : ℝ) ^ 2) := by
  classical
  set l := cleanup G k Δ C
  have hpw : l.Pairwise fun y x ↦ (y ∩ x).card < Δ := by
    simp only [l]
    unfold cleanup
    exact (pairwise_prune _).imp fun h ↦ by simpa using h
  have hcard : ∀ S ∈ l, S.card = k := fun S hS ↦ (isNClique_of_mem_cleanup hS).card_eq
  have hnodup : l.Nodup := by
    refine hpw.imp_of_mem fun {S T} hS _ h hST ↦ ?_
    subst hST
    rw [inter_self, hcard S hS] at h
    omega
  have : Std.Symm fun y x : Finset (Fin n) ↦ (y ∩ x).card < Δ :=
    ⟨fun a b h ↦ by rwa [inter_comm]⟩
  have hall := hpw.forall
  have := card_le_of_inter_le hk hΔk h2 l.toFinset (fun S hS ↦ hcard S (List.mem_toFinset.1 hS))
    fun S hS T hT hST ↦ (hall (List.mem_toFinset.1 hS) (List.mem_toFinset.1 hT) hST).le
  rwa [List.toFinset_card_of_nodup hnodup] at this

end Pruning
