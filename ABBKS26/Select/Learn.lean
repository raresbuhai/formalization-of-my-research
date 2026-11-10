module

public import ABBKS26.Tree.Tree
public import ABBKS26.Select.LearnAuxPartition
public import ABBKS26.Select.LearnAuxSingleton
public import ABBKS26.Select.LearnAuxTransfer
public import ABBKS26.Select.LearnAuxResilience

/-!
# Learning every candidate and selecting a path

For every leaf of the refinement tree, robust learning of each part ([ABBKS26, Fact 3.18]);
the selection step of [ABBKS26, Appendix A] in a simpler form: the first candidate passing
the checks is accepted, and every accepted candidate is accurate.
-/

@[expose] public section

namespace ABBKS26.Select

noncomputable section


open Matrix

open Common _root_.ABBKS26.Tree
variable {n k d : ℕ}

abbrev Learner := {n d : ℕ} → Mode → (Fin n → Fin d → ℚ) →
  Finset (Fin n) → ℕ → Option (Robust.Estimate d)

structure Learned (n d : ℕ) where
  candidate : Candidate n d
  estimates : List (Option (Robust.Estimate d))

def learnAll (learn : Learner) (mode : Mode) (x : Fin n → Fin d → ℚ) (fuel : ℕ)
    (Cs : List (Candidate n d)) : List (Learned n d) :=
  Cs.map fun C ↦ ⟨C, C.blocks.map (fun N ↦ learn mode x N fuel)⟩

def select (params : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (Cs : List (Learned n d)) : Option (Learned n d) :=
  Cs.find? (fun C ↦ C.candidate.path.all (fun e ↦ decide (Verify (params e.depth) x e)))

def LearnerSpec (learn : Learner) : Prop :=
  ∀ {n k d} mode (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d)
    (r : Rounding k d) params fuel,
    Prepared mode M ε w η Δ D ω r params → localBudget mode k n d params ≤ fuel →
    ∀ N j, leakage ω N {j} ≤ (params (k - 1)).leakage →
      w * n / 4 ≤ N.card →
      ∃ E, learn mode (fun l i ↦ r ((ω l).1, (ω l).2.2) i) N fuel = some E ∧
        Robust.Accurate M j E

/-- Every accepted generated history is good and its stored estimates are accurate. -/
theorem accepted_sound
    (ref : Refiner) (learn : Learner) (href : RefineSpec ref) (hl : LearnerSpec learn)
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (fuel : ℕ) (hk : 2 ≤ k) (hp : Prepared mode M ε w η Δ D ω r params)
    (hf : localBudget mode k n d params ≤ fuel) (L : Learned n d)
    (hL : L ∈ learnAll learn mode (fun l i ↦ r ((ω l).1, (ω l).2.2) i) fuel
      (leaves ref mode k params (fun l i ↦ r ((ω l).1, (ω l).2.2) i) fuel))
    (ha : Accepted params (fun l i ↦ r ((ω l).1, (ω l).2.2) i) L.candidate) :
    GoodPartition ω w (leakageBudget params η (k - 1)) L.candidate.blocks ∧
      ∃ π : Equiv.Perm (Fin k), ∀ a : Fin k,
        ∃ E, L.estimates[a.val]? = some (some E) ∧ Robust.Accurate M (π a) E := by
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hL
  have hg := LearnAux.accepted_leaf_good ref href mode M ε w η Δ D ω r params fuel
    hk hp hf C hC ha
  refine ⟨hg, ?_⟩
  have hlen := (leaf_history ref href mode k params _ fuel C hC).1
  obtain ⟨π, hπ⟩ := LearnAux.singleton_partition ω w _ C.blocks hlen hg
  refine ⟨π, fun a ↦ ?_⟩
  have hlt : a.val < C.blocks.length := hlen ▸ a.isLt
  have hleak : leakage ω C.blocks[a.val] {π a} ≤ (params (k - 1)).leakage := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hparams⟩ := hp
    exact (hπ a).1.trans (hparams (k - 1) (by omega)).2.1
  obtain ⟨E, hE, hacc⟩ := hl mode M ε w η Δ D ω r params fuel hp hf
    C.blocks[a.val] (π a) hleak (hπ a).2
  refine ⟨E, ?_, hacc⟩
  change (C.blocks.map (fun N ↦ learn mode _ N fuel))[a.val]? = some (some E)
  rw [List.getElem?_map, List.getElem?_eq_getElem hlt, Option.map_some]
  exact congrArg some hE

/-- Final first-accepted selection succeeds after learning every candidate. -/
theorem accepted_complete
    (ref : Refiner) (learn : Learner) (href : RefineSpec ref) (hl : LearnerSpec learn)
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (fuel : ℕ) (hk : 2 ≤ k) (hp : Prepared mode M ε w η Δ D ω r params)
    (hf : localBudget mode k n d params ≤ fuel) :
    ∃ L, select params (fun l i ↦ r ((ω l).1, (ω l).2.2) i)
      (learnAll learn mode (fun l i ↦ r ((ω l).1, (ω l).2.2) i) fuel
        (leaves ref mode k params (fun l i ↦ r ((ω l).1, (ω l).2.2) i) fuel)) = some L ∧
      ∃ π : Equiv.Perm (Fin k), ∀ a : Fin k,
        ∃ E, L.estimates[a.val]? = some (some E) ∧ Robust.Accurate M (π a) E := by
  let x : Fin n → Fin d → ℚ := fun l i ↦ r ((ω l).1, (ω l).2.2) i
  let Cs := learnAll learn mode x fuel (leaves ref mode k params x fuel)
  let pred (L : Learned n d) : Bool :=
    L.candidate.path.all (fun e ↦ decide (Verify (params e.depth) x e))
  have hpred (L : Learned n d) : pred L = true ↔ Accepted params x L.candidate := by
    simp [pred, Accepted]
  obtain ⟨C, hC, ha, _⟩ := good_path ref href mode M ε w η Δ D ω r params fuel hk hp hf
  have hex : ∃ L ∈ Cs, pred L = true := by
    refine ⟨⟨C, C.blocks.map (fun N ↦ learn mode x N fuel)⟩, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨C, hC, rfl⟩
    · exact (hpred _).mpr ha
  have hsome : (Cs.find? pred).isSome := List.find?_isSome.mpr hex
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨L, hL, ?_⟩
  have hmem : L ∈ Cs := List.mem_of_find?_eq_some hL
  have hacc : Accepted params x L.candidate :=
    (hpred L).mp (List.find?_some hL)
  exact (accepted_sound ref learn href hl mode M ε w η Δ D ω r params fuel hk hp hf
    L hmem hacc).2

end

end ABBKS26.Select
