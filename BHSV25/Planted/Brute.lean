module

public import BHSV25.Planted.Recolor

/-!
# Brute force on the uncolored components

The deterministic part of the last step of [BHSV25, Theorem 7.17]
(`BHSV25.Planted.brute_spec`): let `c` color some vertices as a proper coloring `χ` of `G` does,
and let `U` be its uncolored vertices. If every connected set `C ⊆ U` whose other neighbors are all
colored has `k^|C| ≤ n²`, then brute force (`BHSV25.Planted.brute`) outputs a proper coloring of
all vertices.

* **The closure** (`BHSV25.Planted.clSet`): after `j` rounds, the set reached from `v`; it is
  connected (`BHSV25.Planted.connSet_clSet`), after `n` rounds it is closed under uncolored
  neighbors (`BHSV25.Planted.clSet_closed`), and it is contained in every closed set containing
  `v`. Hence two vertices of one closure have the same closure (`BHSV25.Planted.clSet_eq`): the
  closures are the components of the uncolored vertices.
* **The search**: the coloring `χ` of the closure is among the at most `n²` tuples searched, and
  it has no monochromatic edge, as the neighbors outside the closure are colored as by `χ`. So a
  valid coloring is found, and the vertices of one component take their colors from the same
  one.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Finset

/-! ### Connected sets -/

/-- `C` is **connected**: every proper nonempty part of `C` has a neighbor in the rest of `C`. -/
def ConnSet {V : Type*} [DecidableEq V] (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ A ⊆ C, A.Nonempty → A ≠ C → ∃ u ∈ A, ∃ w ∈ C, w ∉ A ∧ G.Adj u w

theorem ConnSet.mono {V : Type*} [DecidableEq V] {G G' : SimpleGraph V} {C : Finset V}
    (h : ConnSet G C) (hGG' : ∀ u v, G.Adj u v → G'.Adj u v) : ConnSet G' C := by
  intro A hA hne hAC
  obtain ⟨u, hu, w, hw, hwA, huw⟩ := h A hA hne hAC
  exact ⟨u, hu, w, hw, hwA, hGG' u w huw⟩

variable {G : Graph} {k : ℕ}

/-! ### The closure -/

/-- The starting bits of the closure from `v`. -/
def initBits (n v : ℕ) : List Bool := (List.range n).map fun y ↦ decide (y = v)

open Classical in
/-- The set reached from `v` after `j` rounds of the closure. -/
noncomputable def clSet (G : Graph) (k : ℕ) (c : List ℕ) (v j : ℕ) : Finset (Fin G.1) :=
  univ.filter fun y ↦ ((closeStep G.1 k (adjTable G) c)^[j] (initBits G.1 v)).getD y false = true

theorem mem_clSet_zero {c : List ℕ} {v : ℕ} {y : Fin G.1} : y ∈ clSet G k c v 0 ↔ (y : ℕ) = v := by
  rw [clSet, mem_filter, Function.iterate_zero, id, initBits, Net.getD_map_range _ _ _ y.2]
  simp

theorem mem_clSet_iff {c : List ℕ} {v j : ℕ} {y : Fin G.1} :
    y ∈ clSet G k c v j ↔
      ((closeStep G.1 k (adjTable G) c)^[j] (initBits G.1 v)).getD y false = true := by
  rw [clSet, mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨mem_univ _, h⟩⟩

theorem mem_clSet_succ {c : List ℕ} {v j : ℕ} {y : Fin G.1} :
    y ∈ clSet G k c v (j + 1) ↔
      y ∈ clSet G k c v j ∨ (c.getD y k = k ∧ ∃ z ∈ clSet G k c v j, G.2.Adj z y) := by
  rw [mem_clSet_iff, Function.iterate_succ_apply', closeStep, Net.getD_map_range _ _ _ y.2]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_range]
  rw [← mem_clSet_iff]
  constructor
  · rintro (h | ⟨h1, z, hz, h2, h3⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h1, ⟨z, hz⟩, mem_clSet_iff.2 h2, ?_⟩
      have := Alg.adjBit_adjTable G ⟨z, hz⟩ y
      simp only at this
      rw [this] at h3
      simpa using h3
  · rintro (h | ⟨h1, z, hz, h2⟩)
    · exact Or.inl h
    · right
      refine ⟨h1, z, z.2, mem_clSet_iff.1 hz, ?_⟩
      rw [Alg.adjBit_adjTable]; simpa using h2

theorem clSet_mono (c : List ℕ) (v j : ℕ) : clSet G k c v j ⊆ clSet G k c v (j + 1) :=
  fun _ hy ↦ mem_clSet_succ.2 (Or.inl hy)

theorem clSet_mono' (c : List ℕ) (v : ℕ) {i j : ℕ} (hij : i ≤ j) :
    clSet G k c v i ⊆ clSet G k c v j := by
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le hij with h | h
    · exact (ih (by omega)).trans (clSet_mono c v j)
    · rw [h]

/-- The closure is contained in every set containing `v` and closed under uncolored neighbors. -/
theorem clSet_subset (c : List ℕ) (v : Fin G.1) (D : Finset (Fin G.1)) (hvD : v ∈ D)
    (hD : ∀ x ∈ D, ∀ y : Fin G.1, G.2.Adj x y → c.getD y k = k → y ∈ D) (j : ℕ) :
    clSet G k c v j ⊆ D := by
  induction j with
  | zero =>
    intro y hy
    rw [mem_clSet_zero] at hy
    rw [show y = v from Fin.ext hy]; exact hvD
  | succ j ih =>
    intro y hy
    rcases mem_clSet_succ.1 hy with h | ⟨h1, z, hz, h2⟩
    · exact ih h
    · exact hD z (ih hz) y h2 h1

theorem clSet_subset_U (c : List ℕ) {v : Fin G.1} (hv : c.getD v k = k) (j : ℕ) :
    ∀ y ∈ clSet G k c v j, c.getD y k = k := by
  induction j with
  | zero =>
    intro y hy
    rw [mem_clSet_zero] at hy
    rw [show y = v from Fin.ext hy]; exact hv
  | succ j ih =>
    intro y hy
    rcases mem_clSet_succ.1 hy with h | ⟨h1, -⟩
    · exact ih y h
    · exact h1

theorem self_mem_clSet (c : List ℕ) (v : Fin G.1) (j : ℕ) : v ∈ clSet G k c v j :=
  clSet_mono' c v (Nat.zero_le j) (mem_clSet_zero.2 rfl)

/-- **The closure is connected.** -/
theorem connSet_clSet (c : List ℕ) (v : Fin G.1) (j : ℕ) : ConnSet G.2 (clSet G k c v j) := by
  induction j with
  | zero =>
    intro A hA hne hAC
    exfalso
    apply hAC
    obtain ⟨a, ha⟩ := hne
    have hav := mem_clSet_zero.1 (hA ha)
    refine Subset.antisymm hA fun y hy ↦ ?_
    rw [show y = a from Fin.ext ((mem_clSet_zero.1 hy).trans hav.symm)]
    exact ha
  | succ j ih =>
    intro A hA hne hAC
    by_contra hcon
    push Not at hcon
    -- no edge between `A` and the rest
    set S := clSet G k c v j
    by_cases h1 : (A ∩ S).Nonempty
    · by_cases h2 : S ⊆ A
      · -- the rest consists of new vertices, each with a neighbor in `S ⊆ A`
        obtain ⟨y, hy, hyA⟩ := not_subset.1 fun h ↦ hAC (Subset.antisymm hA h)
        rcases mem_clSet_succ.1 hy with h | ⟨-, z, hz, hzy⟩
        · exact hyA (h2 h)
        · exact absurd hzy (hcon z (h2 hz) y hy hyA)
      · obtain ⟨y, hyS, hyA⟩ := not_subset.1 h2
        have hsub : A ∩ S ⊆ S := inter_subset_right
        have hne' : A ∩ S ≠ S := fun h ↦ hyA (inter_subset_left (h ▸ hyS))
        obtain ⟨u, hu, w, hw, hwA, huw⟩ := ih (A ∩ S) hsub h1 hne'
        have hwA' : w ∉ A := fun h ↦ hwA (mem_inter.2 ⟨h, hw⟩)
        exact absurd huw (hcon u (inter_subset_left hu) w (clSet_mono c v j hw) hwA')
    · -- `A` consists of new vertices, each with a neighbor in `S`, outside `A`
      obtain ⟨y, hy⟩ := hne
      rcases mem_clSet_succ.1 (hA hy) with h | ⟨-, z, hz, hzy⟩
      · exact h1 ⟨y, mem_inter.2 ⟨hy, h⟩⟩
      · have hzA : z ∉ A := fun h ↦ h1 ⟨z, mem_inter.2 ⟨h, hz⟩⟩
        exact absurd (G.2.adj_symm hzy) (hcon y hy z (clSet_mono c v j hz) hzA)

/-- **After `n` rounds the closure is closed** under uncolored neighbors. -/
theorem clSet_closed (c : List ℕ) (v : Fin G.1) :
    ∀ x ∈ clSet G k c v G.1, ∀ y : Fin G.1, G.2.Adj x y → c.getD y k = k →
      y ∈ clSet G k c v G.1 := by
  -- a stable round stays stable
  have hstab : ∀ j, clSet G k c v (j + 1) = clSet G k c v j →
      clSet G k c v (j + 2) = clSet G k c v (j + 1) := by
    intro j hj
    ext y
    rw [mem_clSet_succ, hj, ← mem_clSet_succ, hj]
  have hconst : ∀ i, clSet G k c v (i + 1) = clSet G k c v i →
      ∀ m, clSet G k c v (i + m) = clSet G k c v i := by
    intro i hi m
    have hstep : ∀ m, clSet G k c v (i + m + 1) = clSet G k c v (i + m) := by
      intro m
      induction m with
      | zero => exact hi
      | succ m ih => exact hstab (i + m) ih
    induction m with
    | zero => rfl
    | succ m ih => rw [← add_assoc, hstep m, ih]
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, y, hxy, hyU, hy⟩ := hcon
  have hne : clSet G k c v (G.1 + 1) ≠ clSet G k c v G.1 := by
    intro h
    apply hy
    rw [← h]
    exact mem_clSet_succ.2 (Or.inr ⟨hyU, x, hx, hxy⟩)
  have hall : ∀ i ≤ G.1, clSet G k c v (i + 1) ≠ clSet G k c v i := by
    intro i hi heq
    apply hne
    have h1 := hconst i heq (G.1 + 1 - i)
    have h2 := hconst i heq (G.1 - i)
    rw [show i + (G.1 + 1 - i) = G.1 + 1 by omega] at h1
    rw [show i + (G.1 - i) = G.1 by omega] at h2
    rw [h1, h2]
  have hcard : ∀ i ≤ G.1 + 1, i + 1 ≤ (clSet G k c v i).card := by
    intro i hi
    induction i with
    | zero => exact Finset.card_pos.2 ⟨v, self_mem_clSet c v 0⟩
    | succ i ih =>
      have h1 := ih (by omega)
      have h2 : clSet G k c v i ⊂ clSet G k c v (i + 1) :=
        Finset.ssubset_iff_subset_ne.2 ⟨clSet_mono c v i, (hall i (by omega)).symm⟩
      have := Finset.card_lt_card h2
      omega
  have h1 := hcard (G.1 + 1) le_rfl
  have h2 := card_le_univ (clSet G k c v (G.1 + 1))
  rw [Fintype.card_fin] at h2
  omega

/-- **The closures are the components**: a vertex of the closure of an uncolored `v` has the same
closure. -/
theorem clSet_eq (c : List ℕ) {v w : Fin G.1} (hvU : c.getD v k = k)
    (hw : w ∈ clSet G k c v G.1) : clSet G k c w G.1 = clSet G k c v G.1 := by
  have h1 : clSet G k c w G.1 ⊆ clSet G k c v G.1 :=
    clSet_subset c w _ hw (clSet_closed c v) G.1
  refine Subset.antisymm h1 ?_
  -- `v` lies in the closure of `w`
  have hv : v ∈ clSet G k c w G.1 := by
    by_contra hv
    set A := clSet G k c v G.1 ∩ clSet G k c w G.1
    have hA : A ⊆ clSet G k c v G.1 := inter_subset_left
    have hne : A.Nonempty := ⟨w, mem_inter.2 ⟨hw, self_mem_clSet c w G.1⟩⟩
    have hAC : A ≠ clSet G k c v G.1 := fun h ↦ hv
      (inter_subset_right (h ▸ self_mem_clSet c v G.1 : v ∈ A))
    obtain ⟨u, hu, y, hy, hyA, huy⟩ := connSet_clSet c v G.1 A hA hne hAC
    have hyU : c.getD y k = k := clSet_subset_U c hvU G.1 y hy
    exact hyA (mem_inter.2 ⟨hy, clSet_closed c w u (inter_subset_right hu) y huy hyU⟩)
  exact clSet_subset c v _ hv (clSet_closed c w) G.1

/-! ### The search -/

theorem closure_eq_iterate (c : List ℕ) (v : ℕ) :
    closure G.1 k (adjTable G) c v = (closeStep G.1 k (adjTable G) c)^[G.1] (initBits G.1 v) :=
  rfl

theorem mem_bitsToList_closure (c : List ℕ) (v : ℕ) (z : Fin G.1) :
    (z : ℕ) ∈ Alg.bitsToList G.1 (closure G.1 k (adjTable G) c v) ↔ z ∈ clSet G k c v G.1 := by
  rw [Alg.mem_bitsToList, mem_clSet_iff, closure_eq_iterate]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨z.2, h⟩⟩

theorem lt_of_mem_bitsToList {n z : ℕ} {b : List Bool} (h : z ∈ Alg.bitsToList n b) : z < n :=
  (Alg.mem_bitsToList.1 h).1

theorem bitsToList_closure_congr (c : List ℕ) {v w : ℕ}
    (h : clSet G k c v G.1 = clSet G k c w G.1) :
    Alg.bitsToList G.1 (closure G.1 k (adjTable G) c v) =
      Alg.bitsToList G.1 (closure G.1 k (adjTable G) c w) := by
  unfold Alg.bitsToList
  refine List.filter_congr fun z hz ↦ ?_
  rw [List.mem_range] at hz
  have h1 := mem_bitsToList_closure (G := G) (k := k) c v ⟨z, hz⟩
  have h2 := mem_bitsToList_closure (G := G) (k := k) c w ⟨z, hz⟩
  rw [h] at h1
  rw [Alg.mem_bitsToList] at h1 h2
  simp only at h1 h2
  rw [Bool.eq_iff_iff]
  constructor
  · intro h3; exact (h2.2 (h1.1 ⟨hz, h3⟩)).2
  · intro h3; exact (h1.2 (h2.1 ⟨hz, h3⟩)).2

open Classical in
theorem length_bitsToList_closure (c : List ℕ) (v : ℕ) :
    (Alg.bitsToList G.1 (closure G.1 k (adjTable G) c v)).length = (clSet G k c v G.1).card := by
  rw [Alg.bitsToList, ← List.countP_eq_length_filter, Net.countP_range, clSet, card_filter]
  rfl

theorem validAssign_iff (c C σ : List ℕ) (hC : ∀ u ∈ C, u < G.1) :
    validAssign G.1 k (adjTable G) c C σ = true ↔ ∀ u : Fin G.1, (u : ℕ) ∈ C →
      ∀ w : Fin G.1, G.2.Adj u w → assignAt k c C σ u ≠ assignAt k c C σ w := by
  rw [validAssign, List.all_eq_true]
  constructor
  · intro h u hu w huw
    have := List.all_eq_true.1 (h u hu) w (List.mem_range.2 w.2)
    rw [Alg.adjBit_adjTable] at this
    simpa [huw] using this
  · intro h u hu
    rw [List.all_eq_true]
    intro w hw
    rw [List.mem_range] at hw
    have := Alg.adjBit_adjTable G ⟨u, hC u hu⟩ ⟨w, hw⟩
    simp only at this
    rw [this]
    by_cases huw : G.2.Adj ⟨u, hC u hu⟩ ⟨w, hw⟩
    · simpa [huw] using h ⟨u, hC u hu⟩ hu ⟨w, hw⟩ huw
    · simp [huw]

theorem assignAt_of_mem {c C σ : List ℕ} {u : ℕ} (hu : u ∈ C) :
    assignAt k c C σ u = σ.getD (C.idxOf u) 0 := by
  rw [assignAt, ite_eq_left hu]

theorem assignAt_of_not_mem {c C σ : List ℕ} {u : ℕ} (hu : u ∉ C) :
    assignAt k c C σ u = c.getD u k := by
  rw [assignAt, ite_eq_right hu]

/-! ### The brute force -/

/-- **Brute force** [BHSV25, Theorem 7.17, last step]. -/
theorem brute_spec (χ : Fin G.1 → Fin k) (hχ : ∀ u v, G.2.Adj u v → χ u ≠ χ v) (c : List ℕ)
    (hc : ∀ y : Fin G.1, c.getD y k < k → c.getD y k = χ y) (hck : ∀ y : Fin G.1, c.getD y k ≤ k)
    (hsmall : ∀ C : Finset (Fin G.1), (∀ y ∈ C, c.getD y k = k) → C.Nonempty → ConnSet G.2 C →
      (∀ x ∈ C, ∀ y : Fin G.1, G.2.Adj x y → c.getD y k = k → y ∈ C) →
      k ^ C.card ≤ G.1 * G.1) :
    (∀ y : Fin G.1, (brute G.1 k (adjTable G) c).getD y k < k) ∧
    (∀ u v : Fin G.1, G.2.Adj u v →
      (brute G.1 k (adjTable G) c).getD u k ≠ (brute G.1 k (adjTable G) c).getD v k) := by
  set L : ℕ → List ℕ := fun v ↦ Alg.bitsToList G.1 (closure G.1 k (adjTable G) c v) with hL
  have hLlt : ∀ v, ∀ u ∈ L v, u < G.1 := fun v u hu ↦ lt_of_mem_bitsToList hu
  -- for an uncolored `y`, a valid coloring of its closure is found
  have hfound : ∀ y : Fin G.1, c.getD y k = k → ∃ σ,
      ((Tuples.tuples (G.1 * G.1) k (L y).length).find?
        fun σ ↦ validAssign G.1 k (adjTable G) c (L y) σ) = some σ ∧
      validAssign G.1 k (adjTable G) c (L y) σ = true ∧ σ.length = (L y).length ∧
        ∀ x ∈ σ, x < k := by
    intro y hy
    have hsize : k ^ (L y).length ≤ G.1 * G.1 := by
      rw [hL, length_bitsToList_closure]
      exact hsmall _ (clSet_subset_U c hy G.1) ⟨y, self_mem_clSet c y G.1⟩
        (connSet_clSet c y G.1) (clSet_closed c y)
    -- the coloring `χ` of the closure
    set σs := (L y).map fun z ↦ if h : z < G.1 then (χ ⟨z, h⟩ : ℕ) else 0 with hσs
    have hσmem : σs ∈ Tuples.tuples (G.1 * G.1) k (L y).length := by
      rw [Tuples.mem_tuples hsize]
      refine ⟨by rw [hσs, List.length_map], fun x hx ↦ ?_⟩
      rw [hσs, List.mem_map] at hx
      obtain ⟨z, _, rfl⟩ := hx
      split_ifs
      · exact (χ _).2
      · exact lt_of_le_of_lt (Nat.zero_le _) (χ y).2
    have hσat : ∀ u : Fin G.1, (u : ℕ) ∈ L y → assignAt k c (L y) σs u = χ u := by
      intro u hu
      have hidx := List.idxOf_lt_length_of_mem hu
      rw [assignAt_of_mem hu, List.getD_eq_getElem _ _ (by rw [hσs, List.length_map]; exact hidx)]
      simp [hσs, List.getElem_idxOf]
    have hvalid : validAssign G.1 k (adjTable G) c (L y) σs = true := by
      rw [validAssign_iff _ _ _ (hLlt y)]
      intro u hu w huw
      rw [hσat u hu]
      by_cases hw : (w : ℕ) ∈ L y
      · rw [hσat w hw]
        exact fun h ↦ hχ u w huw (Fin.ext h)
      · rw [assignAt_of_not_mem hw]
        have hu' := (mem_bitsToList_closure c y u).1 hu
        have hwU : c.getD w k ≠ k := fun h ↦ hw ((mem_bitsToList_closure c y w).2
          (clSet_closed c y u hu' w huw h))
        have hwk : c.getD w k < k := lt_of_le_of_ne (hck w) hwU
        rw [hc w hwk]
        exact fun h ↦ hχ u w huw (Fin.ext h)
    obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1
      (List.find?_isSome.2 ⟨σs, hσmem, hvalid⟩)
    exact ⟨σ, hσ, List.find?_some hσ, Tuples.mem_tuples_le (List.mem_of_find?_eq_some hσ)⟩
  -- the value of the brute force on the closure of an uncolored vertex
  have hval : ∀ y : Fin G.1, c.getD y k = k → ∃ σ,
      validAssign G.1 k (adjTable G) c (L y) σ = true ∧ (∀ x ∈ σ, x < k) ∧
      σ.length = (L y).length ∧
      ∀ w : Fin G.1, w ∈ clSet G k c y G.1 →
        (brute G.1 k (adjTable G) c).getD w k = assignAt k c (L y) σ w := by
    intro y hy
    obtain ⟨σ, hσ, hv, hlen, hlt⟩ := hfound y hy
    refine ⟨σ, hv, hlt, hlen, fun w hw ↦ ?_⟩
    have hwU : c.getD w k = k := clSet_subset_U c hy G.1 w hw
    have hLw : L w = L y := bitsToList_closure_congr c (clSet_eq c hy hw)
    rw [brute, Net.getD_map_range _ _ _ w.2, ite_eq_left hwU, bruteAt]
    have hLw' : Alg.bitsToList G.1 (closure G.1 k (adjTable G) c w) = L y := hLw
    rw [hLw', hσ, Option.map_some, Option.getD_some,
      assignAt_of_mem ((mem_bitsToList_closure c y w).2 hw)]
  have hself : ∀ y : Fin G.1, (y : ℕ) ∈ L y := fun y ↦
    (mem_bitsToList_closure c y y).2 (self_mem_clSet c y G.1)
  have hbc : ∀ y : Fin G.1, c.getD y k ≠ k → (brute G.1 k (adjTable G) c).getD y k = c.getD y k :=
    fun y hy ↦ by rw [brute, Net.getD_map_range _ _ _ y.2, ite_eq_right hy]
  refine ⟨fun y ↦ ?_, fun u w huw ↦ ?_⟩
  · by_cases hy : c.getD y k = k
    · obtain ⟨σ, -, hlt, hlen, hb⟩ := hval y hy
      rw [hb y (self_mem_clSet c y G.1), assignAt_of_mem (hself y),
        List.getD_eq_getElem _ _ (by rw [hlen]; exact List.idxOf_lt_length_of_mem (hself y))]
      exact hlt _ (List.getElem_mem _)
    · rw [hbc y hy]
      exact lt_of_le_of_ne (hck y) hy
  · by_cases hu : c.getD u k = k
    · obtain ⟨σ, hv, -, -, hb⟩ := hval u hu
      have hvu := (validAssign_iff _ _ _ (hLlt u)).1 hv u (hself u) w huw
      rw [hb u (self_mem_clSet c u G.1)]
      by_cases hwC : w ∈ clSet G k c u G.1
      · rw [hb w hwC]; exact hvu
      · have hwU : c.getD w k ≠ k := fun h ↦
          hwC (clSet_closed c u u (self_mem_clSet c u G.1) w huw h)
        have hwL : (w : ℕ) ∉ L u := fun h ↦ hwC ((mem_bitsToList_closure c u w).1 h)
        rw [hbc w hwU]
        rwa [assignAt_of_not_mem hwL] at hvu
    · by_cases hw : c.getD w k = k
      · obtain ⟨σ, hv, -, -, hb⟩ := hval w hw
        have hvw := (validAssign_iff _ _ _ (hLlt w)).1 hv w (hself w) u (G.2.adj_symm huw)
        have huL : (u : ℕ) ∉ L w := fun h ↦
          hu (clSet_subset_U c hw G.1 u ((mem_bitsToList_closure c w u).1 h))
        rw [hbc u hu, hb w (self_mem_clSet c w G.1)]
        rw [assignAt_of_not_mem huL] at hvw
        exact fun h ↦ hvw h.symm
      · have hu' := lt_of_le_of_ne (hck u) hu
        have hw' := lt_of_le_of_ne (hck w) hw
        rw [hbc u hu, hbc w hw, hc u hu', hc w hw']
        exact fun h ↦ hχ u w huw (Fin.ext h)

end Planted

end BHSV25
