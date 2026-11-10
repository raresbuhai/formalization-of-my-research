module

public import ABBKS26.SoS.Kit

/-!
# Instances of family constraints

Constraint families indexed by auxiliary vectors, as the Hessian constraint of [ABBKS26,
Definition 5.9], instantiated at finitely many vectors; linear certificates transfer to the
instances.
-/

@[expose] public section

namespace ABBKS26.Rounding

noncomputable section


open Matrix

open Common MvPolynomial Matrix
open scoped BigOperators
variable {d : ℕ}

structure FamilySystem (d : ℕ) where
  plain : List (RPoly d)
  families : List (BiPoly d)
  slots : List (Fin families.length)

noncomputable def FamilySystem.instances (A : FamilySystem d)
    (Ξ : Fin A.slots.length → Mat d) : List (RPoly d) :=
  A.plain ++ List.ofFn (fun a ↦ inst (A.families[A.slots[a]]) (Ξ a))

/-- The position of a family slot in the instantiated constraint list. -/
def FamilySystem.slotIndex (A : FamilySystem d)
    (Ξ : Fin A.slots.length → Mat d) (a : Fin A.slots.length) :
    Fin (A.instances Ξ).length :=
  ⟨A.plain.length + a, by simp [FamilySystem.instances]⟩

/-- Linear certificates retain the degree of the family before instantiation. -/
def FamilySystem.DerivesAt (A : FamilySystem d)
    (Ξ : Fin A.slots.length → Mat d) (deg : ℕ) (M : ℝ) (g : RPoly d) : Prop :=
  ∃ P : SoS.Proof (A.instances Ξ) g deg,
    (∀ S, SoS.coeffNorm1 (P.mult S) ≤ M) ∧
    (∀ S, 1 < S.card → P.mult S = 0) ∧
    ∀ a, P.mult {A.slotIndex Ξ a} ≠ 0 →
      (P.mult {A.slotIndex Ξ a}).totalDegree +
        A.families[A.slots[a]].totalDegree ≤ deg

def FamilySystem.Derives (A : FamilySystem d) (deg : ℕ) (M X : ℝ)
    (g : RPoly d) : Prop :=
  ∃ Ξ : Fin A.slots.length → Mat d,
    (∀ a, frobSq (Ξ a) ≤ X ^ 2) ∧ A.DerivesAt Ξ deg M g

namespace FamilySystem.DerivesAt

variable {A : FamilySystem d} {Ξ : Fin A.slots.length → Mat d}
  {deg : ℕ} {M M' : ℝ} {g g' : RPoly d}

theorem derivesNq (h : A.DerivesAt Ξ deg M g) :
    SoS.DerivesNq (A.instances Ξ) deg M 1 g := by
  obtain ⟨P, hn, hq, _⟩ := h
  exact ⟨P, hn, hq⟩

theorem mono (h : A.DerivesAt Ξ deg M g) (hM : M ≤ M') :
    A.DerivesAt Ξ deg M' g := by
  obtain ⟨P, hn, hq, hd⟩ := h
  exact ⟨P, fun S ↦ (hn S).trans hM, hq, hd⟩

theorem congr (h : A.DerivesAt Ξ deg M g) (he : g = g') :
    A.DerivesAt Ξ deg M g' := he ▸ h

theorem add (h : A.DerivesAt Ξ deg M g) (h' : A.DerivesAt Ξ deg M' g') :
    A.DerivesAt Ξ deg (M + M') (g + g') := by
  obtain ⟨P, hn, hq, hd⟩ := h
  obtain ⟨P', hn', hq', hd'⟩ := h'
  refine ⟨P.add P', fun S ↦ (SoS.coeffNorm1_add_le _ _).trans
    (add_le_add (hn S) (hn' S)), ?_, ?_⟩
  · intro S hS
    simp [SoS.Proof.add, hq S hS, hq' S hS]
  · intro a ha
    change P.mult _ + P'.mult _ ≠ 0 at ha
    change (P.mult _ + P'.mult _).totalDegree + _ ≤ _
    by_cases hz : P.mult {A.slotIndex Ξ a} = 0
    · simpa [hz] using hd' a (by simpa [hz] using ha)
    by_cases hz' : P'.mult {A.slotIndex Ξ a} = 0
    · simpa [hz'] using hd a hz
    have := hd a hz
    have := hd' a hz'
    have := totalDegree_add (P.mult {A.slotIndex Ξ a}) (P'.mult {A.slotIndex Ξ a})
    omega

theorem smul {c : ℝ} (h : A.DerivesAt Ξ deg M g) (hc : 0 ≤ c) :
    A.DerivesAt Ξ deg (c * M) (C c * g) := by
  obtain ⟨P, hn, hq, hd⟩ := h
  refine ⟨(P.mulSOS (SoS.IsSOS.const hc)).weaken (by simp), ?_, ?_, ?_⟩
  · intro S
    change SoS.coeffNorm1 (C c * P.mult S) ≤ _
    rw [SoS.coeffNorm1_C_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (hn S) hc
  · intro S hS
    change C c * P.mult S = 0
    rw [hq S hS, mul_zero]
  · intro a ha
    change C c * P.mult _ ≠ 0 at ha
    have hz : P.mult {A.slotIndex Ξ a} ≠ 0 := fun hz ↦ ha (by rw [hz, mul_zero])
    have hdeg := hd a hz
    have hm := totalDegree_mul (C c) (P.mult {A.slotIndex Ξ a})
    simp only [totalDegree_C, zero_add] at hm
    exact (Nat.add_le_add_right hm _).trans hdeg

theorem ofIsSOS (A : FamilySystem d) (Ξ : Fin A.slots.length → Mat d)
    {p : RPoly d} (hp : IsSumSq p) (hd : p.totalDegree ≤ deg)
    (hn : SoS.coeffNorm1 p ≤ M) : A.DerivesAt Ξ deg M p := by
  classical
  refine ⟨SoS.Proof.ofIsSOS (A.instances Ξ)
    (by simpa only [SoS.IsSOS, SoS.toReal_real] using hp) hd, ?_, ?_, ?_⟩
  · intro S
    simp only [SoS.Proof.ofIsSOS]
    split_ifs
    · exact hn
    · simpa using (SoS.coeffNorm1_nonneg p).trans hn
  · intro S hS
    have hs : S ≠ ∅ := by intro hs; simp [hs] at hS
    simp [SoS.Proof.ofIsSOS, hs]
  · intro a ha
    simp [SoS.Proof.ofIsSOS] at ha

theorem of_plain {f : RPoly d} (hf : f ∈ A.plain) (hd : f.totalDegree ≤ deg) :
    A.DerivesAt Ξ deg 1 f := by
  classical
  obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hf
  let i : Fin (A.instances Ξ).length := ⟨j, by
    simp [FamilySystem.instances]; omega⟩
  have he : (A.instances Ξ).get i = A.plain.get j := by
    simp [i, FamilySystem.instances, List.getElem_append_left j.isLt]
  rw [← he] at hd ⊢
  refine ⟨SoS.Proof.assumption (A.instances Ξ) i hd, ?_, ?_, ?_⟩
  · intro S
    simp only [SoS.Proof.assumption]
    split_ifs <;> simp [SoS.coeffNorm1_one]
  · intro S hS
    have hs : S ≠ {i} := by intro hs; simp [hs] at hS
    simp [SoS.Proof.assumption, hs]
  · intro a ha
    have hs : A.slotIndex Ξ a ≠ i := by
      intro hs
      have hv := congrArg Fin.val hs
      dsimp [FamilySystem.slotIndex, i] at hv
      omega
    simp [SoS.Proof.assumption, hs] at ha

end FamilySystem.DerivesAt

def FamilySystem.FeasibleComplement (A : FamilySystem d) (R : Mat d) (M : ℝ) : Prop :=
  (∀ f ∈ A.plain, SoS.DerivesNq ball f.totalDegree M 1 (subst (1 - R) f)) ∧
  (∀ F ∈ A.families, SoS.DerivesNq [1 - liftV nsq] F.totalDegree M 1
    (substV (1 - R) F))

def FamilySystem.Valid (A : FamilySystem d) (deg : ℕ) : Prop :=
  1 - nsq ∈ A.plain ∧ (∀ f ∈ A.plain, f.totalDegree ≤ deg) ∧
    (∀ F ∈ A.families, F.totalDegree ≤ deg)

def plainSystem (A : List (RPoly d)) : FamilySystem d := ⟨A, [], []⟩


/-- Substitution preserves the family transfer certificate. -/
theorem instance_sos
    (F G : BiPoly d) (κ : ℝ) (Ξ : Mat d) (h : IsSumSq (G - C κ * F)) :
    IsSumSq (inst G Ξ - C κ * inst F Ξ) := by
  simpa only [inst, map_sub, map_mul, aeval_C, algebraMap_eq] using
    SoS.isSumSq_map (aeval (Sum.elim (fun i ↦ lin (Ξ i)) X)) h

end

end ABBKS26.Rounding
