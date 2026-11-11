module

public import BHSV25.UG.Value
import Mathlib.Data.List.GetD

/-!
# Left-regularizing a bipartite Unique Games instance

`BHSV25.UG.regularize ℓ G`, for an instance with constraints `cs` and `A = ℓ |cs|`: one new left
vertex `j` for each position `j` of `cs`, a copy of the left vertex `x` of the constraint at `j`
(`BHSV25.UG.lv`), with each constraint at `x` repeated `⌊A / d⌋` times and the first one `A mod d`
more times, for the degree `d` of `x` (`BHSV25.UG.block`); the right vertices are those of `G`.
The new left vertices all have degree `A`, parallel constraints are copies of one constraint, and
a vertex `x` of degree `d` has `d` copies, so the copies carry the weights of the constraints:

* the value changes by at most `1/ℓ` in either direction (`BHSV25.UG.ugValue_le_regularize`,
  `BHSV25.UG.regularize_le_ugValue`): a copy of `x` labeled `a` satisfies
  `⌊A / d⌋ F_x(a) + (A mod d) [a satisfies the first]` constraints, `F_x(a)` the number of
  constraints at `x` that `a` satisfies, within `d` of `(A / d) F_x(a)`; summed over the `d`
  copies of each `x` this is `A` times the satisfied constraints of `G`, up to `∑ d ≤ |cs|²`,
  that is up to a `|cs| / A = 1/ℓ` fraction. For soundness every copy of `x` is relabeled by a
  label maximizing `F_x`, which loses nothing;
* on valid instances whose parallel constraints agree, the result is valid, left-regular, and its
  parallel constraints agree (`BHSV25.UG.regularize_good`).

This is Khot and Regev's regularization [KR08, Lemmas 3.3 and 3.4] in one step, with the copies
indexed by the constraints.
-/

@[expose] public section

namespace BHSV25.UG

open Finset UniqueGames BK

/-- The default constraint. -/
abbrev dflt : UGConstraint := ((0, 0), [])

/-- The left vertex of the constraint at position `j`. -/
def lv (cs : List UGConstraint) (j : ℕ) : ℕ := (cs.getD j dflt).1.1

/-- The constraints of the new left vertex `j`, a copy of the left vertex `x` of the constraint at
position `j`: each constraint at `x` repeated `⌊A / d⌋` times and the first one `A mod d` more
times, for the degree `d` of `x` and `A = ℓ |cs|`. -/
def block (ℓ : ℕ) (cs : List UGConstraint) (j : ℕ) : List UGConstraint :=
  ((nbrs cs (lv cs j)).flatMap fun c ↦
      List.replicate (ℓ * cs.length / (nbrs cs (lv cs j)).length) ((j, c.1.2), c.2)) ++
    List.replicate (ℓ * cs.length % (nbrs cs (lv cs j)).length)
      ((j, ((nbrs cs (lv cs j)).headD dflt).1.2), ((nbrs cs (lv cs j)).headD dflt).2)

/-- **Left-regularization**: one left vertex per constraint, a copy of its left vertex, of degree
`ℓ |cs|`. -/
def regularize (ℓ : ℕ) (G : UGInstance) : UGInstance :=
  (G.2.2.2.length, G.2.1, G.2.2.1, (List.range G.2.2.2.length).flatMap (block ℓ G.2.2.2))

/-! ### Sums -/

theorem list_range_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ((List.range n).map g).sum = ∑ j ∈ range n, g j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- The number of constraints at `x` that the label `a` satisfies, for the right labeling `τ`. -/
noncomputable def satAt (cs : List UGConstraint) (τ : ℕ → ℕ) (x a : ℕ) : ℝ :=
  ((nbrs cs x).map fun c ↦ ind (a = c.2.getD (τ c.1.2) 0)).sum

theorem satAt_nonneg (cs : List UGConstraint) (τ : ℕ → ℕ) (x a : ℕ) : 0 ≤ satAt cs τ x a :=
  List.sum_nonneg fun _ h ↦ by
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 h
    exact ind_nonneg _

theorem satAt_le (cs : List UGConstraint) (τ : ℕ → ℕ) (x a : ℕ) :
    satAt cs τ x a ≤ (nbrs cs x).length := by
  unfold satAt
  rw [← list_sum_const_one]
  exact List.sum_le_sum fun c _ ↦ ind_le_one _

theorem satAt_nil {cs : List UGConstraint} {τ : ℕ → ℕ} {x : ℕ} (h : (nbrs cs x).length = 0)
    (a : ℕ) : satAt cs τ x a = 0 := by
  unfold satAt
  rw [List.length_eq_zero_iff.1 h]
  simp

/-- The satisfied constraints of `G`, grouped by left vertex. -/
theorem ugSatisfied_eq_sum_satAt {G : UGInstance} (hv : UGValid G) (σ τ : ℕ → ℕ) :
    (ugSatisfied G σ τ : ℝ) = ∑ x ∈ range G.1, satAt G.2.2.2 τ x (σ x) := by
  rw [ugSatisfied_eq_sum, sum_nbrs hv]
  refine sum_congr rfl fun x _ ↦ ?_
  unfold satAt
  congr 1
  refine List.map_congr_left fun c hc ↦ ?_
  rw [(List.mem_filter.1 hc).2 |> of_decide_eq_true]

/-- A sum over the positions of `cs`, of a function of the left vertex, grouped by left vertex. -/
theorem sum_lv {G : UGInstance} (hv : UGValid G) (g : ℕ → ℝ) :
    ∑ j ∈ range G.2.2.2.length, g (lv G.2.2.2 j) =
      ∑ x ∈ range G.1, ((nbrs G.2.2.2 x).length : ℝ) * g x := by
  have h1 : ∑ j ∈ range G.2.2.2.length, g (lv G.2.2.2 j) = (G.2.2.2.map fun c ↦ g c.1.1).sum :=
    sum_range_getD G.2.2.2 dflt fun c ↦ g c.1.1
  rw [h1, sum_nbrs hv]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [List.map_congr_left (g := fun _ ↦ g x) fun c hc ↦ by
    rw [(List.mem_filter.1 hc).2 |> of_decide_eq_true], List.map_const', List.sum_replicate,
    nsmul_eq_mul]

/-! ### The blocks -/

section Block

variable {ℓ : ℕ} {G : UGInstance}

theorem getD_mem {cs : List UGConstraint} {j : ℕ} (hj : j < cs.length) : cs.getD j dflt ∈ cs := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem mem_nbrs_lv {cs : List UGConstraint} {j : ℕ} (hj : j < cs.length) :
    cs.getD j dflt ∈ nbrs cs (lv cs j) :=
  List.mem_filter.2 ⟨getD_mem hj, by simp [lv]⟩

theorem nbrs_lv_pos {cs : List UGConstraint} {j : ℕ} (hj : j < cs.length) :
    0 < (nbrs cs (lv cs j)).length :=
  List.length_pos_of_mem (mem_nbrs_lv hj)

theorem nbrs_length_le (cs : List UGConstraint) (x : ℕ) : (nbrs cs x).length ≤ cs.length :=
  List.length_filter_le _ _

theorem headD_mem {l : List UGConstraint} (h : 0 < l.length) : l.headD dflt ∈ l := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_length_pos h
  simp

/-- The constraints of the block `j` are copies of constraints at `lv j`, with left vertex `j`. -/
theorem mem_block {cs : List UGConstraint} {j : ℕ} (hj : j < cs.length) {c : UGConstraint}
    (hc : c ∈ block ℓ cs j) :
    c.1.1 = j ∧ ∃ c' ∈ nbrs cs (lv cs j), c.1.2 = c'.1.2 ∧ c.2 = c'.2 := by
  unfold block at hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨c', hc', hcc⟩ := List.mem_flatMap.1 hc
    rw [List.eq_of_mem_replicate hcc]
    exact ⟨rfl, c', hc', rfl, rfl⟩
  · rw [List.eq_of_mem_replicate hc]
    exact ⟨rfl, _, headD_mem (nbrs_lv_pos hj), rfl, rfl⟩

theorem length_block (cs : List UGConstraint) (j : ℕ) :
    (block ℓ cs j).length = ℓ * cs.length := by
  unfold block
  rw [List.length_append, List.length_flatMap, List.length_replicate]
  simp only [List.length_replicate, List.map_const', List.sum_replicate, smul_eq_mul]
  rw [Nat.div_add_mod]

/-- The satisfied constraints of a block labeled `a`. -/
theorem block_sum (cs : List UGConstraint) (j a : ℕ) (τ : ℕ → ℕ) :
    ((block ℓ cs j).map fun c ↦ ind (a = c.2.getD (τ c.1.2) 0)).sum =
      ((ℓ * cs.length / (nbrs cs (lv cs j)).length : ℕ) : ℝ) * satAt cs τ (lv cs j) a +
      ((ℓ * cs.length % (nbrs cs (lv cs j)).length : ℕ) : ℝ) *
        ind (a = ((nbrs cs (lv cs j)).headD dflt).2.getD
          (τ ((nbrs cs (lv cs j)).headD dflt).1.2) 0) := by
  unfold block satAt
  rw [List.map_append, List.sum_append, sum_flatMap_map, List.map_replicate, List.sum_replicate,
    nsmul_eq_mul, ← List.sum_map_mul_left]
  congr 2
  refine List.map_congr_left fun c _ ↦ ?_
  rw [List.map_replicate, List.sum_replicate, nsmul_eq_mul]

/-- The satisfied constraints of a block are within `d` of `(A / d) F_x(a)`. -/
theorem block_sum_bounds {cs : List UGConstraint} {j : ℕ} (hj : j < cs.length) (a : ℕ)
    (τ : ℕ → ℕ) :
    (ℓ * cs.length : ℝ) / (nbrs cs (lv cs j)).length * satAt cs τ (lv cs j) a -
        (nbrs cs (lv cs j)).length ≤
      ((block ℓ cs j).map fun c ↦ ind (a = c.2.getD (τ c.1.2) 0)).sum ∧
    ((block ℓ cs j).map fun c ↦ ind (a = c.2.getD (τ c.1.2) 0)).sum ≤
      (ℓ * cs.length : ℝ) / (nbrs cs (lv cs j)).length * satAt cs τ (lv cs j) a +
        (nbrs cs (lv cs j)).length := by
  rw [block_sum]
  set d := (nbrs cs (lv cs j)).length with hd
  set A := ℓ * cs.length with hA
  have hd0 : 0 < d := nbrs_lv_pos hj
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  have hF0 := satAt_nonneg cs τ (lv cs j) a
  have hFd := satAt_le cs τ (lv cs j) a
  rw [← hd] at hFd
  have hi0 := ind_nonneg (a = ((nbrs cs (lv cs j)).headD dflt).2.getD
    (τ ((nbrs cs (lv cs j)).headD dflt).1.2) 0)
  have hi1 := ind_le_one (a = ((nbrs cs (lv cs j)).headD dflt).2.getD
    (τ ((nbrs cs (lv cs j)).headD dflt).1.2) 0)
  -- `A = d ⌊A / d⌋ + A mod d`, with `A mod d < d`
  have hdm : (d : ℝ) * ((A / d : ℕ) : ℝ) + ((A % d : ℕ) : ℝ) = A := by
    exact_mod_cast Nat.div_add_mod A d
  have hmod : ((A % d : ℕ) : ℝ) + 1 ≤ d := by exact_mod_cast Nat.mod_lt A hd0
  have hmod0 : (0 : ℝ) ≤ ((A % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hq : ((A / d : ℕ) : ℝ) = (A : ℝ) / d - ((A % d : ℕ) : ℝ) / d := by
    field_simp
    linarith
  have hAd : ((A : ℕ) : ℝ) = (ℓ : ℝ) * cs.length := by rw [hA]; push_cast; ring
  rw [← hAd]
  constructor
  · -- `⌊A/d⌋ F ≥ (A/d) F - (A mod d)/d · F ≥ (A/d) F - d`
    have h1 : ((A % d : ℕ) : ℝ) / d * satAt cs τ (lv cs j) a ≤ d := by
      calc ((A % d : ℕ) : ℝ) / d * satAt cs τ (lv cs j) a ≤ 1 * d := by
            refine mul_le_mul ?_ hFd hF0 zero_le_one
            rw [div_le_one hdr]
            linarith
        _ = d := one_mul _
    rw [hq]
    nlinarith
  · have h1 : ((A % d : ℕ) : ℝ) * ind (a = ((nbrs cs (lv cs j)).headD dflt).2.getD
        (τ ((nbrs cs (lv cs j)).headD dflt).1.2) 0) ≤ d := by
      nlinarith
    have h2 : ((A / d : ℕ) : ℝ) * satAt cs τ (lv cs j) a ≤
        (A : ℝ) / d * satAt cs τ (lv cs j) a := by
      refine mul_le_mul_of_nonneg_right ?_ hF0
      rw [hq]
      have : (0 : ℝ) ≤ ((A % d : ℕ) : ℝ) / d := by positivity
      linarith
    linarith

end Block

/-! ### Validity and regularity -/

theorem mem_regularize {ℓ : ℕ} {G : UGInstance} {c : UGConstraint}
    (hc : c ∈ (regularize ℓ G).2.2.2) :
    ∃ j < G.2.2.2.length, c ∈ block ℓ G.2.2.2 j := by
  simpa [regularize] using hc

theorem regularize_valid {ℓ : ℕ} {G : UGInstance} (hv : UGValid G) :
    UGValid (regularize ℓ G) := by
  intro c hc
  obtain ⟨j, hj, hcj⟩ := mem_regularize hc
  obtain ⟨h1, c', hc', h2, h3⟩ := mem_block hj hcj
  obtain ⟨-, g2, g3, g4, g5⟩ := hv c' (List.mem_filter.1 hc').1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]; exact hj
  · rw [h2]; exact g2
  · rw [h3]; exact g3
  · rw [h3]; exact g4
  · rw [h3]; exact g5

theorem regularize_consistent {ℓ : ℕ} {G : UGInstance} (hc : UGConsistent G) :
    UGConsistent (regularize ℓ G) := by
  intro c₁ hc₁ c₂ hc₂ h12
  obtain ⟨j₁, hj₁, hcj₁⟩ := mem_regularize hc₁
  obtain ⟨j₂, hj₂, hcj₂⟩ := mem_regularize hc₂
  obtain ⟨e₁, c₁', hc₁', f₁, g₁⟩ := mem_block hj₁ hcj₁
  obtain ⟨e₂, c₂', hc₂', f₂, g₂⟩ := mem_block hj₂ hcj₂
  have hj : j₁ = j₂ := by rw [← e₁, ← e₂, congrArg Prod.fst h12]
  subst hj
  have hl₁ := of_decide_eq_true (List.mem_filter.1 hc₁').2
  have hl₂ := of_decide_eq_true (List.mem_filter.1 hc₂').2
  have hpair : c₁'.1 = c₂'.1 :=
    Prod.ext (hl₁.trans hl₂.symm) (f₁.symm.trans ((congrArg Prod.snd h12).trans f₂))
  rw [g₁, g₂]
  exact hc _ (List.mem_filter.1 hc₁').1 _ (List.mem_filter.1 hc₂').1 hpair

theorem nbrs_regularize {ℓ : ℕ} {G : UGInstance} {j : ℕ} (hj : j < G.2.2.2.length) :
    ((regularize ℓ G).2.2.2.filter fun c ↦ c.1.1 = j).length = ℓ * G.2.2.2.length := by
  simp only [regularize]
  rw [List.filter_flatMap, List.length_flatMap]
  have h : ∀ i ∈ List.range G.2.2.2.length,
      ((block ℓ G.2.2.2 i).filter fun c ↦ c.1.1 = j).length =
        if i = j then ℓ * G.2.2.2.length else 0 := by
    intro i hi
    have hi' := List.mem_range.1 hi
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, List.filter_eq_self.2 fun c hc ↦ by simp [(mem_block hi' hc).1],
        length_block]
    · rw [ite_eq_right hij, List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc
      simp [(mem_block hi' hc).1, hij]
  rw [List.map_congr_left h, list_range_sum]
  simp [hj]

/-- **The regularized instance**: valid, with agreeing parallel constraints, left-regular, with
the labels of `G`. -/
theorem regularize_good {ℓ R : ℕ} {G : UGInstance} (hv : UGValid G) (hR : G.2.2.1 = R)
    (hc : UGConsistent G) : Good R (regularize ℓ G) :=
  ⟨regularize_valid hv, hR, regularize_consistent hc,
    ⟨ℓ * G.2.2.2.length, fun _ hj ↦ nbrs_regularize hj⟩⟩

/-! ### The value -/

theorem length_regularize {ℓ : ℕ} (G : UGInstance) :
    (regularize ℓ G).2.2.2.length = G.2.2.2.length * (ℓ * G.2.2.2.length) := by
  simp only [regularize]
  rw [List.length_flatMap, List.map_congr_left (g := fun _ ↦ ℓ * G.2.2.2.length)
    fun j _ ↦ length_block _ j, List.map_const', List.sum_replicate,
    List.length_range, smul_eq_mul]

/-- The satisfied constraints of the regularized instance, block by block. -/
theorem ugSatisfied_regularize {ℓ : ℕ} (G : UGInstance) (σ' τ : ℕ → ℕ) :
    (ugSatisfied (regularize ℓ G) σ' τ : ℝ) = ∑ j ∈ range G.2.2.2.length,
      ((block ℓ G.2.2.2 j).map fun c ↦ ind (σ' j = c.2.getD (τ c.1.2) 0)).sum := by
  rw [ugSatisfied_eq_sum]
  simp only [regularize]
  rw [sum_flatMap_map, list_range_sum]
  refine sum_congr rfl fun j hj ↦ ?_
  congr 1
  refine List.map_congr_left fun c hc ↦ ?_
  rw [(mem_block (mem_range.1 hj) hc).1]

/-- The grouped main term: `∑_j (A / d_{x_j}) F_{x_j}(σ x_j) = A · #satisfied(σ, τ)`. -/
theorem sum_main {ℓ : ℕ} {G : UGInstance} (hv : UGValid G) (σ τ : ℕ → ℕ) :
    ∑ j ∈ range G.2.2.2.length, (ℓ * G.2.2.2.length : ℝ) / (nbrs G.2.2.2 (lv G.2.2.2 j)).length *
        satAt G.2.2.2 τ (lv G.2.2.2 j) (σ (lv G.2.2.2 j)) =
      (ℓ * G.2.2.2.length : ℝ) * ugSatisfied G σ τ := by
  rw [sum_lv hv (fun x ↦ (ℓ * G.2.2.2.length : ℝ) / (nbrs G.2.2.2 x).length *
    satAt G.2.2.2 τ x (σ x)), ugSatisfied_eq_sum_satAt hv, mul_sum]
  refine sum_congr rfl fun x _ ↦ ?_
  rcases Nat.eq_zero_or_pos (nbrs G.2.2.2 x).length with h0 | hpos
  · rw [satAt_nil h0, h0]
    simp
  · have : ((nbrs G.2.2.2 x).length : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp

/-- The error term: `∑_j d_{x_j} ≤ |cs|²`. -/
theorem sum_err {G : UGInstance} :
    ∑ j ∈ range G.2.2.2.length, ((nbrs G.2.2.2 (lv G.2.2.2 j)).length : ℝ) ≤
      (G.2.2.2.length : ℝ) * G.2.2.2.length := by
  calc ∑ j ∈ range G.2.2.2.length, ((nbrs G.2.2.2 (lv G.2.2.2 j)).length : ℝ)
      ≤ ∑ _j ∈ range G.2.2.2.length, (G.2.2.2.length : ℝ) :=
        sum_le_sum fun j _ ↦ by exact_mod_cast nbrs_length_le _ _
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]

/-- **Completeness**: `val(G) - 1/ℓ ≤ val(regularize ℓ G)`. -/
theorem ugValue_le_regularize {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {G : UGInstance} (hv : UGValid G) :
    ugValue G ≤ ugValue (regularize ℓ G) + 1 / ℓ := by
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hinv : (0 : ℝ) ≤ 1 / ℓ := by positivity
  have hv0 := ugValue_nonneg (regularize ℓ G)
  refine ugValue_le' (by linarith) fun σ τ hσ hτ ↦ ?_
  set L := G.2.2.2.length with hL
  rcases Nat.eq_zero_or_pos L with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, div_zero]
    linarith
  -- the labeling of the copies
  set σ' : ℕ → ℕ := fun j ↦ if j < L then σ (lv G.2.2.2 j) else 0 with hσ'
  have hσ'lab : IsLab (regularize ℓ G).1 (regularize ℓ G).2.2.1 σ' := by
    refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
    · have hj' : j < L := hj
      simp only [hσ', hj', ↓reduceIte]
      exact hσ.1 _ (hv _ (getD_mem hj')).1
    · have hj' : ¬ j < L := not_lt.2 hj
      simp only [hσ', hj', ↓reduceIte]
  have hval := le_ugValue' (regularize ℓ G) hσ'lab hτ
  rw [ugSatisfied_regularize, length_regularize] at hval
  have hlow : (ℓ * L : ℝ) * ugSatisfied G σ τ - L * L ≤ ∑ j ∈ range L,
      ((block ℓ G.2.2.2 j).map fun c ↦ ind (σ' j = c.2.getD (τ c.1.2) 0)).sum := by
    rw [← sum_main hv σ τ]
    have hb : ∀ j ∈ range L, (ℓ * L : ℝ) / (nbrs G.2.2.2 (lv G.2.2.2 j)).length *
        satAt G.2.2.2 τ (lv G.2.2.2 j) (σ (lv G.2.2.2 j)) -
          (nbrs G.2.2.2 (lv G.2.2.2 j)).length ≤
        ((block ℓ G.2.2.2 j).map fun c ↦ ind (σ' j = c.2.getD (τ c.1.2) 0)).sum := by
      intro j hj
      have hj' := mem_range.1 hj
      have h := (block_sum_bounds (ℓ := ℓ) hj' (σ (lv G.2.2.2 j)) τ).1
      simpa only [hσ', hj', ↓reduceIte] using h
    have := sum_le_sum hb
    rw [sum_sub_distrib] at this
    linarith [sum_err (G := G)]
  have hLr : (0 : ℝ) < L := by exact_mod_cast hpos
  have hA : (0 : ℝ) < (L : ℝ) * (ℓ * L) := by positivity
  rw [← hL] at hval
  push_cast at hval
  rw [div_le_iff₀ hLr]
  have h1 : (ℓ * L : ℝ) * ugSatisfied G σ τ - L * L ≤
      ugValue (regularize ℓ G) * (L * (ℓ * L)) := by
    rw [div_le_iff₀ hA] at hval
    linarith
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have h2 : (ugSatisfied G σ τ : ℝ) ≤ (ugValue (regularize ℓ G) + 1 / ℓ) * L := by
    have h3 : (ℓ * L : ℝ) * ((ugValue (regularize ℓ G) + 1 / ℓ) * L) =
        ugValue (regularize ℓ G) * (L * (ℓ * L)) + L * L := by
      field_simp
    nlinarith
  exact h2

/-- **Soundness**: `val(regularize ℓ G) ≤ val(G) + 1/ℓ`. -/
theorem regularize_le_ugValue {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {G : UGInstance} (hv : UGValid G) :
    ugValue (regularize ℓ G) ≤ ugValue G + 1 / ℓ := by
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hinv : (0 : ℝ) ≤ 1 / ℓ := by positivity
  have hv0 := ugValue_nonneg G
  refine ugValue_le' (by linarith) fun σ' τ hσ' hτ ↦ ?_
  set L := G.2.2.2.length with hL
  rw [length_regularize]
  rcases Nat.eq_zero_or_pos L with h0 | hpos
  · rw [← hL, h0]
    simp only [Nat.cast_zero, zero_mul, div_zero]
    linarith
  have hR : 0 < G.2.2.1 := lt_of_le_of_lt (Nat.zero_le _) (hσ'.1 0 hpos)
  -- the best label of each left vertex
  have hbest : ∀ x, ∃ a < G.2.2.1, ∀ b < G.2.2.1, satAt G.2.2.2 τ x b ≤ satAt G.2.2.2 τ x a := by
    intro x
    obtain ⟨a, ha, hmax⟩ := exists_max_image (range G.2.2.1) (satAt G.2.2.2 τ x)
      ⟨0, mem_range.2 hR⟩
    exact ⟨a, mem_range.1 ha, fun b hb ↦ hmax b (mem_range.2 hb)⟩
  choose best hbest_lt hbest_max using hbest
  set σ : ℕ → ℕ := fun x ↦ if x < G.1 then best x else 0 with hσdef
  have hσlab : IsLab G.1 G.2.2.1 σ := by
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · simp only [hσdef, hx, ↓reduceIte]
      exact hbest_lt x
    · simp only [hσdef, not_lt.2 hx, ↓reduceIte]
  have hval := le_ugValue' G hσlab hτ
  have hup : ∑ j ∈ range L,
      ((block ℓ G.2.2.2 j).map fun c ↦ ind (σ' j = c.2.getD (τ c.1.2) 0)).sum ≤
        (ℓ * L : ℝ) * ugSatisfied G σ τ + L * L := by
    rw [← sum_main hv σ τ]
    have hb : ∀ j ∈ range L,
        ((block ℓ G.2.2.2 j).map fun c ↦ ind (σ' j = c.2.getD (τ c.1.2) 0)).sum ≤
        (ℓ * L : ℝ) / (nbrs G.2.2.2 (lv G.2.2.2 j)).length *
          satAt G.2.2.2 τ (lv G.2.2.2 j) (σ (lv G.2.2.2 j)) +
          (nbrs G.2.2.2 (lv G.2.2.2 j)).length := by
      intro j hj
      have hj' := mem_range.1 hj
      have h := (block_sum_bounds (ℓ := ℓ) hj' (σ' j) τ).2
      have hx : lv G.2.2.2 j < G.1 := (hv _ (getD_mem hj')).1
      have hσx : σ (lv G.2.2.2 j) = best (lv G.2.2.2 j) := by simp [hσdef, hx]
      have hle : satAt G.2.2.2 τ (lv G.2.2.2 j) (σ' j) ≤
          satAt G.2.2.2 τ (lv G.2.2.2 j) (σ (lv G.2.2.2 j)) := by
        rw [hσx]
        exact hbest_max _ _ (hσ'.1 j hj')
      have hc0 : (0 : ℝ) ≤ (ℓ * L : ℝ) / (nbrs G.2.2.2 (lv G.2.2.2 j)).length := by positivity
      nlinarith
    have := sum_le_sum hb
    rw [sum_add_distrib] at this
    linarith [sum_err (G := G)]
  rw [ugSatisfied_regularize]
  have hLr : (0 : ℝ) < L := by exact_mod_cast hpos
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hA : (0 : ℝ) < (L : ℝ) * (ℓ * L) := by positivity
  push_cast
  rw [div_le_iff₀ hA]
  rw [div_le_iff₀ hLr] at hval
  have h3 : (ugValue G + 1 / ℓ) * (L * (ℓ * L)) = ℓ * L * (ugValue G * L) + L * L := by
    field_simp
  rw [h3]
  nlinarith

end BHSV25.UG
