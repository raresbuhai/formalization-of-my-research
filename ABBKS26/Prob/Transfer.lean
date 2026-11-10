module

public import ABBKS26.Prob.Basic

/-!
# Conditioning on the labels: from i.i.d. Gaussian samples to clusters

Given the labels, the standardized clean points `gₗ = Σ_{ℓₗ}^{-1/2} (yₗ - μ_{ℓₗ})` of a sample are
independent standard Gaussian vectors. So an event about an i.i.d. standard Gaussian sample of a
fixed size `m` transfers to the clusters: if for every `m` a measurable set `B m` of `m`-tuples
has probability at most `β` under `stdGaussian^m` (Mathlib's `stdGaussian` on
`EuclideanSpace ℝ (Fin d)`), then with probability at least `1 - k β` no cluster's standardized
points, listed in increasing order of index, lie in `B`.

* `ABBKS26.reindex s x`: the entries of `x` at the indices in `s`, in increasing order, indexed by
  `Fin s.card`; `ABBKS26.clusterPts M ω j`: the standardized clean points with label `j`.
* `ABBKS26.measurableSet_clusterPts_mem`, `ABBKS26.measurableSet_exists_clusterPts_mem`: the events
  are measurable.
* `ABBKS26.IsCorruption.pi_clusterPts_mem_le`: the points of one cluster lie in `B` with
  probability at most `β`.
* `ABBKS26.IsCorruption.pi_exists_clusterPts_mem_le`: the points of some cluster lie in `B` with
  probability at most `k β`.

To use it only for large clusters, take `B m = ∅` for small `m` (small clusters are excluded by
the cluster-size event `ABBKS26.GoodCounts`).

The proof: the law of the labels and standardized points is `(labelLaw w ⊗ stdGaussian)^n`
(`ABBKS26.noiseLaw_eq_prod`), which is `labelLaw w^n ⊗ stdGaussian^n`
(`measurePreserving_arrowProdEquivProdArrow`); for a fixed label vector the re-indexed points of
a cluster have law `stdGaussian^m` (`ABBKS26.Transfer.pi_map_comp_injective`), and summing over the
label vectors gives the bound (`ABBKS26.Transfer.prod_setOf_mem_le`).
-/

@[expose] public section

namespace ABBKS26

open MeasureTheory ProbabilityTheory

variable {k d : ℕ}

/-- The entries of `x` at the indices in `s`, in increasing order of index. -/
def reindex {X : Type*} {n : ℕ} (s : Finset (Fin n)) (x : Fin n → X) : Fin s.card → X :=
  fun t ↦ x (s.orderEmbOfFin rfl t)

theorem measurable_reindex {X : Type*} [MeasurableSpace X] {n : ℕ} (s : Finset (Fin n)) :
    Measurable (reindex (X := X) s) :=
  Measurable.of_eval fun t ↦ measurable_pi_apply (s.orderEmbOfFin rfl t)

/-- The standardized clean points `Σⱼ^{-1/2} (yₗ - μⱼ)` of the sample points with label `j`, in
increasing order of index. -/
noncomputable def clusterPts (M : Mixture k d) {n : ℕ} (ω : Fin n → Triple k d) (j : Fin k) :
    Fin (cluster (labels ω) j).card → EuclideanSpace ℝ (Fin d) :=
  reindex (cluster (labels ω) j) (stdClean M ω)

namespace Transfer

/-- Restricting an i.i.d. family to an injectively re-indexed subfamily gives an i.i.d. family. -/
theorem pi_map_comp_injective {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {ι ι' : Type*} [Fintype ι] [Fintype ι'] {e : ι' → ι}
    (he : Function.Injective e) :
    (Measure.pi fun _ : ι ↦ μ).map (fun x t ↦ x (e t)) = Measure.pi fun _ : ι' ↦ μ := by
  have h1 : iIndepFun (fun (i : ι) (x : ι → X) ↦ x i) (Measure.pi fun _ ↦ μ) :=
    iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id
  have h2 := h1.precomp he
  rw [iIndepFun_iff_map_fun_eq_pi_map fun t ↦ (measurable_pi_apply (e t)).aemeasurable] at h2
  rw [h2]
  congr 1
  funext t
  exact (measurePreserving_eval (fun _ : ι ↦ μ) (e t)).map_eq

theorem setOf_mem_eq {α X : Type*} (Q : α → Set X) :
    {p : α × X | p.2 ∈ Q p.1} = ⋃ a, {a} ×ˢ Q a := by
  ext ⟨a, x⟩
  simp

theorem measurableSet_setOf_mem {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X] {Q : α → Set X}
    (hQ : ∀ a, MeasurableSet (Q a)) : MeasurableSet {p : α × X | p.2 ∈ Q p.1} := by
  rw [setOf_mem_eq]
  exact MeasurableSet.iUnion fun a ↦ (measurableSet_singleton a).prod (hQ a)

/-- If each section `Q a` has `ρ`-measure at most `b`, so has `{(a, x) | x ∈ Q a}` under
`ν ⊗ ρ`, for a probability measure `ν` on a finite type. -/
theorem prod_setOf_mem_le {α X : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X] (ν : Measure α) [IsProbabilityMeasure ν]
    (ρ : Measure X) [SigmaFinite ρ] (Q : α → Set X) {b : ENNReal} (hb : ∀ a, ρ (Q a) ≤ b) :
    (ν.prod ρ) {p : α × X | p.2 ∈ Q p.1} ≤ b := by
  have := Fintype.ofFinite α
  rw [setOf_mem_eq]
  calc (ν.prod ρ) (⋃ a, {a} ×ˢ Q a) ≤ ∑ a, (ν.prod ρ) ({a} ×ˢ Q a) := measure_iUnion_fintype_le _ _
    _ = ∑ a, ν {a} * ρ (Q a) := by simp only [Measure.prod_prod]
    _ ≤ ∑ a, ν {a} * b := by gcongr with a; exact hb a
    _ = b := by
        rw [← Finset.sum_mul, sum_measure_singleton, Finset.coe_univ, measure_univ, one_mul]

end Transfer

open Transfer

/-- The event that the re-indexed points of cluster `j`, for label and point pairs `z`, lie in
`B`. -/
private def pairsEvent {n : ℕ} (B : ∀ m, Set (Fin m → EuclideanSpace ℝ (Fin d))) (j : Fin k) :
    Set (Fin n → Fin k × EuclideanSpace ℝ (Fin d)) :=
  {z | reindex (cluster (fun l ↦ (z l).1) j) (fun l ↦ (z l).2) ∈
    B (cluster (fun l ↦ (z l).1) j).card}

private theorem pairsEvent_eq {n : ℕ} (B : ∀ m, Set (Fin m → EuclideanSpace ℝ (Fin d)))
    (j : Fin k) :
    pairsEvent (n := n) B j = MeasurableEquiv.arrowProdEquivProdArrow _ _ _ ⁻¹'
      {p | p.2 ∈ reindex (cluster p.1 j) ⁻¹' B (cluster p.1 j).card} := by
  ext z
  rfl

private theorem measurableSet_pairsEvent {n : ℕ} {B : ∀ m, Set (Fin m → EuclideanSpace ℝ (Fin d))}
    (hB : ∀ m, MeasurableSet (B m)) (j : Fin k) : MeasurableSet (pairsEvent (n := n) B j) := by
  rw [pairsEvent_eq]
  exact (measurableSet_setOf_mem (α := Fin n → Fin k) (X := Fin n → EuclideanSpace ℝ (Fin d))
    (Q := fun ℓ ↦ reindex (cluster ℓ j) ⁻¹' B (cluster ℓ j).card)
    fun ℓ ↦ (hB _).preimage (measurable_reindex _)).preimage (MeasurableEquiv.measurable _)

private theorem preimage_pairsEvent (M : Mixture k d) {n : ℕ}
    (B : ∀ m, Set (Fin m → EuclideanSpace ℝ (Fin d))) (j : Fin k) :
    stdPairs M ⁻¹' pairsEvent (n := n) B j =
      {ω | clusterPts M ω j ∈ B (cluster (labels ω) j).card} :=
  preimage_stdPairs_setOf M fun ℓ g ↦ reindex (cluster ℓ j) g ∈ B (cluster ℓ j).card

/-- **The cluster event is measurable.** -/
theorem measurableSet_clusterPts_mem (M : Mixture k d) {n : ℕ}
    {B : ∀ m, Set (Fin m → EuclideanSpace ℝ (Fin d))} (hB : ∀ m, MeasurableSet (B m))
    (j : Fin k) :
    MeasurableSet {ω : Fin n → Triple k d | clusterPts M ω j ∈ B (cluster (labels ω) j).card} := by
  rw [← preimage_pairsEvent]
  exact (measurableSet_pairsEvent hB j).preimage (measurable_stdPairs M n)

/-- **The event for some cluster is measurable.** -/
theorem measurableSet_exists_clusterPts_mem (M : Mixture k d) {n : ℕ}
    {B : ∀ m, Set (Fin m → EuclideanSpace ℝ (Fin d))} (hB : ∀ m, MeasurableSet (B m)) :
    MeasurableSet {ω : Fin n → Triple k d |
      ∃ j, clusterPts M ω j ∈ B (cluster (labels ω) j).card} := by
  rw [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun j ↦ measurableSet_clusterPts_mem M hB j

variable {M : Mixture k d} {ε : ℝ} {P : Measure (Triple k d)}

/-- **Transfer for one cluster.** For an `ε`-corruption of a valid mixture: if for every `m` the
measurable set `B m` of `m`-tuples has probability at most `β` under the product of `m` standard
Gaussians, then the standardized clean points of cluster `j`, in increasing order of index, lie in
`B` with probability at most `β`. -/
theorem IsCorruption.pi_clusterPts_mem_le (hM : M.Valid) (hP : IsCorruption M ε P) {n : ℕ}
    {B : ∀ m, Set (Fin m → EuclideanSpace ℝ (Fin d))} (hB : ∀ m, MeasurableSet (B m)) {β : ℝ}
    (hβ : ∀ m, (Measure.pi fun _ : Fin m ↦ stdGaussian (EuclideanSpace ℝ (Fin d))).real (B m) ≤ β)
    (j : Fin k) :
    (Measure.pi fun _ : Fin n ↦ P).real
      {ω | clusterPts M ω j ∈ B (cluster (labels ω) j).card} ≤ β := by
  have hβ0 : 0 ≤ β := measureReal_nonneg.trans (hβ 0)
  have := isProbabilityMeasure_labelLaw hM.sum_w hM.nonneg_w
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγ
  rw [measureReal_def, ← preimage_pairsEvent, hP.pi_preimage_stdPairs hM
    (measurableSet_pairsEvent hB j), noiseLaw_eq_prod hM.sum_w hM.nonneg_w, pairsEvent_eq,
    (measurePreserving_arrowProdEquivProdArrow _ _ _ (fun _ ↦ labelLaw M.w)
      (fun _ ↦ γ)).measure_preimage_equiv]
  refine ENNReal.toReal_le_of_le_ofReal hβ0 (prod_setOf_mem_le _ _
    (fun ℓ ↦ reindex (cluster ℓ j) ⁻¹' B (cluster ℓ j).card) fun ℓ ↦ ?_)
  have hinj : Function.Injective ((cluster ℓ j).orderEmbOfFin rfl) :=
    ((cluster ℓ j).orderEmbOfFin rfl).injective
  have hmap := pi_map_comp_injective γ (ι := Fin n) hinj
  rw [← Measure.map_apply (measurable_reindex _) (hB _)]
  change ((Measure.pi fun _ : Fin n ↦ γ).map fun x t ↦ x ((cluster ℓ j).orderEmbOfFin rfl t))
    (B _) ≤ _
  rw [hmap, ← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (hβ _)

/-- **Transfer for all clusters.** For an `ε`-corruption of a valid mixture: if for every `m` the
measurable set `B m` of `m`-tuples has probability at most `β` under the product of `m` standard
Gaussians, then for some component `j` the standardized clean points of cluster `j`, in increasing
order of index, lie in `B` with probability at most `k β`. -/
theorem IsCorruption.pi_exists_clusterPts_mem_le (hM : M.Valid) (hP : IsCorruption M ε P)
    {n : ℕ} {B : ∀ m, Set (Fin m → EuclideanSpace ℝ (Fin d))} (hB : ∀ m, MeasurableSet (B m))
    {β : ℝ}
    (hβ : ∀ m, (Measure.pi fun _ : Fin m ↦ stdGaussian (EuclideanSpace ℝ (Fin d))).real (B m) ≤ β) :
    (Measure.pi fun _ : Fin n ↦ P).real
      {ω | ∃ j, clusterPts M ω j ∈ B (cluster (labels ω) j).card} ≤ k * β := by
  have := hP.isProbabilityMeasure_pi hM n
  rw [Set.ofPred_exists]
  calc (Measure.pi fun _ : Fin n ↦ P).real
        (⋃ j, {ω | clusterPts M ω j ∈ B (cluster (labels ω) j).card})
      ≤ ∑ j, (Measure.pi fun _ : Fin n ↦ P).real
          {ω | clusterPts M ω j ∈ B (cluster (labels ω) j).card} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin k, β := Finset.sum_le_sum fun j _ ↦ hP.pi_clusterPts_mem_le hM hB hβ j
    _ = k * β := by simp

end ABBKS26
