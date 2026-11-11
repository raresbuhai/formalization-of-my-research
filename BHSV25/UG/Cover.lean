module

public import BHSV25.UG.Value
import Mathlib.Data.List.GetD

/-!
# The double cover of a Unique Games instance on a graph

`BHSV25.UG.cover G`: a left and a right copy of every vertex of `G`, and for each constraint
`((u, v), π)` of `G` the constraints `((u, v), π)` and `((v, u), π⁻¹)` (`BHSV25.UG.invTable`).
On valid simple instances it is valid with agreeing parallel constraints
(`BHSV25.UG.cover_valid`, `BHSV25.UG.cover_consistent`; the two copies of a constraint join
different pairs since `u ≠ v`), and

* **completeness**: a labeling `σ` of `G` labels both sides and satisfies twice as many of the
  twice as many constraints (`BHSV25.UG.ugGraphValue_le_cover`);
* **soundness**: for a labeling `(σ, τ)` of the cover, labeling each vertex from `σ` or from `τ`
  (`BHSV25.UG.mix`), over all `2^n` choices, satisfies each constraint `((u, v), π)` of `G` at
  least as often as a quarter of the choices times the number of its two copies satisfied (`u`
  from `σ` and `v` from `τ` for the first, the reverse for the second;
  `BHSV25.UG.quarter`). So some choice satisfies a quarter of the constraints of the cover:
  `val(cover G) ≤ 2 val(G)` (`BHSV25.UG.cover_le_two_mul`).
-/

@[expose] public section

namespace BHSV25.UG

open Finset UniqueGames BK

/-- The table of the inverse permutation: `π⁻¹(a)` is the position of `a` in `π`. -/
def invTable (π : List ℕ) : List ℕ := (List.range π.length).map fun a ↦ π.idxOf a

/-- The **double cover** of an instance on a graph: a left and a right copy of every vertex, and
for each constraint `((u, v), π)` the constraints `((u, v), π)` and `((v, u), π⁻¹)`. -/
def cover (G : UGGraphInstance) : UGInstance :=
  (G.1, G.1, G.2.1, G.2.2.flatMap fun c ↦ [c, ((c.1.2, c.1.1), invTable c.2)])

/-! ### The inverse table -/

section Inverse

variable {R : ℕ} {π : List ℕ}

theorem length_invTable (π : List ℕ) : (invTable π).length = π.length := by simp [invTable]

theorem getD_invTable {a : ℕ} (ha : a < π.length) : (invTable π).getD a 0 = π.idxOf a := by
  simp [invTable, List.getD_eq_getElem?_getD, ha]

theorem mem_of_lt (hlen : π.length = R) (hnd : π.Nodup) (hlt : ∀ a ∈ π, a < R) {a : ℕ}
    (ha : a < R) : a ∈ π :=
  List.idxOf_lt_length_iff.1 (hlen ▸ (perm_table hlen hnd hlt ⟨a, ha⟩).1)

theorem invTable_valid (hlen : π.length = R) (hnd : π.Nodup) (hlt : ∀ a ∈ π, a < R) :
    (invTable π).length = R ∧ (invTable π).Nodup ∧ ∀ a ∈ invTable π, a < R := by
  refine ⟨by rw [length_invTable, hlen], ?_, ?_⟩
  · refine List.Nodup.map_on (fun a ha b _ h ↦ ?_) List.nodup_range
    rw [List.mem_range, hlen] at ha
    exact (List.idxOf_inj (mem_of_lt hlen hnd hlt ha)).1 h
  · intro a ha
    simp only [invTable, List.mem_map, List.mem_range] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    rw [hlen] at hb
    rw [← hlen]
    exact List.idxOf_lt_length_iff.2 (mem_of_lt hlen hnd hlt hb)

/-- `π⁻¹(a) = b` exactly when `π(b) = a`. -/
theorem invTable_iff (hlen : π.length = R) (hnd : π.Nodup) (hlt : ∀ a ∈ π, a < R) {a b : ℕ}
    (ha : a < R) (hb : b < R) : (invTable π).getD a 0 = b ↔ π.getD b 0 = a := by
  rw [getD_invTable (hlen ▸ ha)]
  constructor
  · rintro rfl
    exact (perm_table hlen hnd hlt ⟨a, ha⟩).2.1
  · intro h
    have hb' : b < π.length := hlen ▸ hb
    rw [List.getD_eq_getElem _ _ hb'] at h
    rw [← h, hnd.idxOf_getElem]

end Inverse

/-! ### Validity -/

theorem mem_cover {G : UGGraphInstance} {c : UGConstraint} (hc : c ∈ (cover G).2.2.2) :
    ∃ d ∈ G.2.2, c = d ∨ c = ((d.1.2, d.1.1), invTable d.2) := by
  simpa [cover] using hc

theorem cover_valid {G : UGGraphInstance} (hv : UGGraphValid G) : UGValid (cover G) := by
  intro c hc
  obtain ⟨d, hd, h | h⟩ := mem_cover hc <;> rw [h]
  · obtain ⟨h1, h2, -, h4, h5, h6⟩ := hv d hd
    exact ⟨h1, h2, h4, h5, h6⟩
  · obtain ⟨h1, h2, -, h4, h5, h6⟩ := hv d hd
    obtain ⟨i1, i2, i3⟩ := invTable_valid h4 h5 h6
    exact ⟨h2, h1, i1, i2, i3⟩

/-- On a simple instance, two constraints joining the same two vertices are equal. -/
theorem eq_of_simple {G : UGGraphInstance} (hs : UGGraphSimple G) {d d' : UGConstraint}
    (hd : d ∈ G.2.2) (hd' : d' ∈ G.2.2) (h : d.1 = d'.1 ∨ d.1 = d'.1.swap) : d = d' := by
  by_contra hne
  have : Std.Symm (fun c c' : UGConstraint ↦ c.1 ≠ c'.1 ∧ c.1 ≠ c'.1.swap) :=
    ⟨fun c c' h ↦ ⟨fun e ↦ h.1 e.symm, fun e ↦ h.2 (by rw [e, Prod.swap_swap])⟩⟩
  have h2 := List.Pairwise.forall hs hd hd' hne
  rcases h with h | h
  · exact h2.1 h
  · exact h2.2 h

theorem cover_consistent {G : UGGraphInstance} (hv : UGGraphValid G) (hs : UGGraphSimple G) :
    UGConsistent (cover G) := by
  intro c hc c' hc' hcc
  obtain ⟨d, hd, h | h⟩ := mem_cover hc <;> obtain ⟨d', hd', h' | h'⟩ := mem_cover hc' <;>
    rw [h, h'] at hcc ⊢ <;> (try dsimp only at hcc ⊢)
  · rw [eq_of_simple hs hd hd' (Or.inl hcc)]
  · have he := eq_of_simple hs hd hd' (Or.inr hcc)
    subst he
    exact absurd (congrArg Prod.fst hcc) (hv d hd).2.2.1
  · have he := eq_of_simple hs hd hd' (Or.inr (by rw [← hcc]; rfl))
    subst he
    exact absurd (congrArg Prod.snd hcc) (hv d hd).2.2.1
  · have h1 : d.1 = d'.1 := Prod.ext (congrArg Prod.snd hcc) (congrArg Prod.fst hcc)
    rw [eq_of_simple hs hd hd' (Or.inl h1)]

/-! ### The satisfied constraints -/

theorem length_cover (G : UGGraphInstance) : (cover G).2.2.2.length = 2 * G.2.2.length := by
  obtain ⟨n, R, cs⟩ := G
  simp only [cover]
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [List.flatMap_cons, ih]; ring

theorem ugSatisfied_cover (G : UGGraphInstance) (σ τ : ℕ → ℕ) :
    (ugSatisfied (cover G) σ τ : ℝ) = (G.2.2.map fun d ↦ ind (σ d.1.1 = d.2.getD (τ d.1.2) 0) +
      ind (σ d.1.2 = (invTable d.2).getD (τ d.1.1) 0)).sum := by
  rw [ugSatisfied_eq_sum]
  simp only [cover]
  rw [sum_flatMap_map]
  simp

/-! ### Completeness -/

/-- **Completeness**: a labeling of `G` on both sides satisfies the same fraction of the cover. -/
theorem ugGraphValue_le_cover {G : UGGraphInstance} (hv : UGGraphValid G) :
    ugGraphValue G ≤ ugValue (cover G) := by
  refine ugGraphValue_le' (ugValue_nonneg _) fun σ hσ ↦ ?_
  refine le_of_eq_of_le ?_ (le_ugValue' (cover G) (σ := σ) (τ := σ) hσ hσ)
  rw [ugGraphSatisfied_eq_sum, ugSatisfied_cover, length_cover]
  have hmap : (G.2.2.map fun d ↦ ind (σ d.1.1 = d.2.getD (σ d.1.2) 0) +
      ind (σ d.1.2 = (invTable d.2).getD (σ d.1.1) 0)) =
      G.2.2.map fun d ↦ 2 * ind (σ d.1.1 = d.2.getD (σ d.1.2) 0) := by
    refine List.map_congr_left fun d hd ↦ ?_
    obtain ⟨h1, h2, -, h4, h5, h6⟩ := hv d hd
    have hiff : (σ d.1.2 = (invTable d.2).getD (σ d.1.1) 0) ↔
        (σ d.1.1 = d.2.getD (σ d.1.2) 0) :=
      eq_comm.trans ((invTable_iff h4 h5 h6 (hσ.1 _ h1) (hσ.1 _ h2)).trans eq_comm)
    rw [congrArg ind (propext hiff)]
    ring
  rw [hmap, List.sum_map_mul_left]
  push_cast
  rcases eq_or_ne G.2.2.length 0 with h0 | h0
  · simp [h0]
  · have hL : (G.2.2.length : ℝ) ≠ 0 := by exact_mod_cast h0
    field_simp

/-! ### Soundness -/

/-- Each vertex `w < n` labeled from `σ` if `s w` and from `τ` otherwise. -/
def mix (n : ℕ) (s : Fin n → Bool) (σ τ : ℕ → ℕ) (w : ℕ) : ℕ :=
  if h : w < n then (if s ⟨w, h⟩ then σ w else τ w) else 0

theorem mix_isLab {n R : ℕ} (s : Fin n → Bool) {σ τ : ℕ → ℕ} (hσ : IsLab n R σ)
    (hτ : IsLab n R τ) : IsLab n R (mix n s σ τ) := by
  refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
  · simp only [mix, hw, ↓reduceDIte]
    split_ifs
    · exact hσ.1 w hw
    · exact hτ.1 w hw
  · simp [mix, not_lt.2 hw]

/-- A quarter of the `2^n` choices of `s : Fin n → Bool` have given values at two distinct
vertices. -/
theorem four_mul_card {n : ℕ} {u v : Fin n} (huv : u ≠ v) (a b : Bool) :
    4 * (univ.filter fun s : Fin n → Bool ↦ s u = a ∧ s v = b).card = 2 ^ n := by
  classical
  let ψ (p q : Bool) (s : Fin n → Bool) : Fin n → Bool :=
    Function.update (Function.update s u (xor (s u) p)) v (xor (s v) q)
  have hψu : ∀ p q s, ψ p q s u = xor (s u) p := by
    intro p q s
    simp [ψ, Function.update_of_ne huv]
  have hψv : ∀ p q s, ψ p q s v = xor (s v) q := by
    intro p q s
    simp [ψ]
  have hψψ : ∀ p q s, ψ p q (ψ p q s) = s := by
    intro p q s
    funext w
    by_cases hwv : w = v
    · subst hwv
      rw [hψv, hψv]
      simp
    · by_cases hwu : w = u
      · subst hwu
        rw [hψu, hψu]
        simp
      · simp [ψ, Function.update_of_ne hwv, Function.update_of_ne hwu]
  have heq : ∀ a b, (univ.filter fun s : Fin n → Bool ↦ s u = a ∧ s v = b).card =
      (univ.filter fun s : Fin n → Bool ↦ s u = true ∧ s v = true).card := by
    intro a b
    refine card_nbij' (ψ (xor a true) (xor b true)) (ψ (xor a true) (xor b true)) ?_ ?_ ?_ ?_
    · intro s hs
      rw [mem_coe, mem_filter] at hs ⊢
      refine ⟨mem_univ _, ?_⟩
      rw [hψu, hψv, hs.2.1, hs.2.2]
      cases a <;> cases b <;> simp
    · intro s hs
      rw [mem_coe, mem_filter] at hs ⊢
      refine ⟨mem_univ _, ?_⟩
      rw [hψu, hψv, hs.2.1, hs.2.2]
      cases a <;> cases b <;> simp
    · intro s _
      exact hψψ _ _ s
    · intro s _
      exact hψψ _ _ s
  have htot := card_eq_sum_card_fiberwise (f := fun s : Fin n → Bool ↦ (s u, s v))
    (s := univ) (t := univ) fun _ _ ↦ mem_coe.2 (mem_univ _)
  rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at htot
  have hfib : ∀ p : Bool × Bool, (univ.filter fun s : Fin n → Bool ↦ (s u, s v) = p).card =
      (univ.filter fun s : Fin n → Bool ↦ s u = true ∧ s v = true).card := by
    intro p
    rw [← heq p.1 p.2]
    exact congrArg card (filter_congr fun s _ ↦ by simp [Prod.ext_iff])
  rw [sum_congr rfl fun p _ ↦ hfib p, sum_const, card_univ, Fintype.card_prod,
    Fintype.card_bool, smul_eq_mul] at htot
  rw [heq, htot]

/-- **A quarter of the choices**: summed over the `2^n` mixed labelings, a constraint
`((u, v), π)` of `G` is satisfied at least `2^n / 4` times for each of its two copies in the
cover satisfied by `(σ, τ)`. -/
theorem quarter {n R : ℕ} {σ τ : ℕ → ℕ} (hσ : IsLab n R σ) (hτ : IsLab n R τ)
    {d : UGConstraint} (h1 : d.1.1 < n) (h2 : d.1.2 < n) (h3 : d.1.1 ≠ d.1.2)
    (h4 : d.2.length = R) (h5 : d.2.Nodup) (h6 : ∀ a ∈ d.2, a < R) :
    (2 : ℝ) ^ n * (ind (σ d.1.1 = d.2.getD (τ d.1.2) 0) +
      ind (σ d.1.2 = (invTable d.2).getD (τ d.1.1) 0)) ≤
      4 * ∑ s : Fin n → Bool, ind (mix n s σ τ d.1.1 = d.2.getD (mix n s σ τ d.1.2) 0) := by
  classical
  have huv : (⟨d.1.1, h1⟩ : Fin n) ≠ ⟨d.1.2, h2⟩ := fun h ↦ h3 (congrArg Fin.val h)
  obtain ⟨T, hTdef⟩ : ∃ T : Finset (Fin n → Bool),
      T = univ.filter fun s ↦ s ⟨d.1.1, h1⟩ = true ∧ s ⟨d.1.2, h2⟩ = false := ⟨_, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : Finset (Fin n → Bool),
      F = univ.filter fun s ↦ s ⟨d.1.1, h1⟩ = false ∧ s ⟨d.1.2, h2⟩ = true := ⟨_, rfl⟩
  have hT : (4 : ℝ) * T.card = 2 ^ n := by
    rw [hTdef]
    exact_mod_cast four_mul_card huv true false
  have hF : (4 : ℝ) * F.card = 2 ^ n := by
    rw [hFdef]
    exact_mod_cast four_mul_card huv false true
  have hdisj : Disjoint T F := by
    rw [hTdef, hFdef]
    exact disjoint_filter.2 fun s _ h h' ↦ by rw [h.1] at h'; exact Bool.noConfusion h'.1
  have hsub := sum_le_sum_of_subset_of_nonneg (subset_univ (T ∪ F))
    (f := fun s ↦ ind (mix n s σ τ d.1.1 = d.2.getD (mix n s σ τ d.1.2) 0))
    fun _ _ _ ↦ ind_nonneg _
  rw [sum_union hdisj] at hsub
  have hTs : ∀ s ∈ T, ind (mix n s σ τ d.1.1 = d.2.getD (mix n s σ τ d.1.2) 0) =
      ind (σ d.1.1 = d.2.getD (τ d.1.2) 0) := by
    intro s hs
    rw [hTdef, mem_filter] at hs
    have hu : mix n s σ τ d.1.1 = σ d.1.1 := by simp [mix, h1, hs.2.1]
    have hv : mix n s σ τ d.1.2 = τ d.1.2 := by simp [mix, h2, hs.2.2]
    rw [hu, hv]
  have hFs : ∀ s ∈ F, ind (mix n s σ τ d.1.1 = d.2.getD (mix n s σ τ d.1.2) 0) =
      ind (σ d.1.2 = (invTable d.2).getD (τ d.1.1) 0) := by
    intro s hs
    rw [hFdef, mem_filter] at hs
    have hu : mix n s σ τ d.1.1 = τ d.1.1 := by simp [mix, h1, hs.2.1]
    have hv : mix n s σ τ d.1.2 = σ d.1.2 := by simp [mix, h2, hs.2.2]
    rw [hu, hv]
    exact congrArg ind (propext (eq_comm.trans
      ((invTable_iff h4 h5 h6 (hτ.1 _ h1) (hσ.1 _ h2)).symm.trans eq_comm)))
  rw [sum_congr rfl hTs, sum_congr rfl hFs, sum_const, sum_const, nsmul_eq_mul,
    nsmul_eq_mul] at hsub
  calc (2 : ℝ) ^ n * (ind (σ d.1.1 = d.2.getD (τ d.1.2) 0) +
        ind (σ d.1.2 = (invTable d.2).getD (τ d.1.1) 0)) =
      4 * (T.card * ind (σ d.1.1 = d.2.getD (τ d.1.2) 0) +
        F.card * ind (σ d.1.2 = (invTable d.2).getD (τ d.1.1) 0)) := by
        rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, hT, hF]
    _ ≤ _ := by linarith

/-- Some mixed labeling satisfies a quarter of the number of constraints of the cover satisfied
by `(σ, τ)`. -/
theorem exists_mix {G : UGGraphInstance} (hv : UGGraphValid G) {σ τ : ℕ → ℕ}
    (hσ : IsLab G.1 G.2.1 σ) (hτ : IsLab G.1 G.2.1 τ) :
    ∃ s : Fin G.1 → Bool,
      (ugSatisfied (cover G) σ τ : ℝ) ≤ 4 * ugGraphSatisfied G (mix G.1 s σ τ) := by
  have key : (2 : ℝ) ^ G.1 * ugSatisfied (cover G) σ τ ≤
      4 * ∑ s : Fin G.1 → Bool, (ugGraphSatisfied G (mix G.1 s σ τ) : ℝ) := by
    rw [ugSatisfied_cover]
    simp_rw [ugGraphSatisfied_eq_sum]
    rw [sum_list_comm, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
    refine List.sum_le_sum fun d hd ↦ ?_
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv d hd
    exact quarter hσ hτ h1 h2 h3 h4 h5 h6
  by_contra h
  push Not at h
  have hlt : 4 * ∑ s : Fin G.1 → Bool, (ugGraphSatisfied G (mix G.1 s σ τ) : ℝ) <
      ∑ _s : Fin G.1 → Bool, (ugSatisfied (cover G) σ τ : ℝ) := by
    rw [mul_sum]
    exact sum_lt_sum_of_nonempty univ_nonempty fun s _ ↦ h s
  rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul] at hlt
  push_cast at hlt
  linarith

/-- **Soundness**: `val(cover G) ≤ 2 val(G)`. -/
theorem cover_le_two_mul {G : UGGraphInstance} (hv : UGGraphValid G) :
    ugValue (cover G) ≤ 2 * ugGraphValue G := by
  refine ugValue_le' (by linarith [ugGraphValue_nonneg G]) fun σ τ hσ hτ ↦ ?_
  obtain ⟨s, hs⟩ := exists_mix hv hσ hτ
  have hval := le_ugGraphValue G (mix_isLab s hσ hτ)
  rw [length_cover]
  push_cast
  rcases eq_or_ne G.2.2.length 0 with h0 | h0
  · rw [h0]
    simp only [Nat.cast_zero, mul_zero, div_zero]
    linarith [ugGraphValue_nonneg G]
  · have hL : (0 : ℝ) < G.2.2.length := by exact_mod_cast Nat.pos_of_ne_zero h0
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hL] at hval
    nlinarith

end BHSV25.UG
