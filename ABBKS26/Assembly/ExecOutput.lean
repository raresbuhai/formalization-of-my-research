module

public import ABBKS26.Assembly.ExecTests

/-! # Guarded pairwise-test construction and output -/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common _root_.ABBKS26.Tree Select
open Turing.MultiTapeTM ComputableInPolyTime

/-- Check the learned list before initiating any component-count loop. -/
def finishL (T : TestCode) (mode : Mode) (d k : ℕ) (Δ : ℚ) (pts : Points) (fuel : ℕ)
    (estimates : List (Option EstimateL)) : Output :=
  if estimates.length ≠ k ∨ estimates.any Option.isNone then List.replicate pts.length 0 else
    let Es := estimates.map fun E ↦ E.getD ([], [])
    let tests := Es.map fun A ↦ Es.map fun B ↦ T.run mode ((d, Δ, A, B), fuel)
    reclusterL d Es.length tests pts

noncomputable def finish {n d : ℕ} (tests : TestBuilder) (mode : Mode) (k : ℕ) (Δ : ℚ)
    (pts : Fin n → Fin d → ℚ) (fuel : ℕ) (estimates : List (Option (Robust.Estimate d))) :
    Output :=
  if estimates.length ≠ k ∨ estimates.any Option.isNone then List.replicate n 0 else
    let E := fun a : Fin k ↦ (estimates[a.val]?.bind id).getD (⟨0, 1⟩ : Robust.Estimate d)
    recluster (fun a b ↦ tests mode Δ (E a) (E b) fuel) pts

/-- The finite estimate enumeration is exactly the one used by `execute`. -/
theorem finish_agrees (T : TestCode) (hT : TestSpecL T) {n d : ℕ}
    (mode : Mode) (k : ℕ) (Δ : ℚ) (pts : Fin n → Fin d → ℚ) (fuel : ℕ)
    (estimates : List (Option (Robust.Estimate d))) :
    finishL T mode d k Δ (pointsOf pts) fuel (estimates.map (Option.map estimateList)) =
      finish T.tests mode k Δ pts fuel estimates := by
  have hany : (estimates.map (Option.map estimateList)).any Option.isNone =
      estimates.any Option.isNone := by
    simp only [List.any_map]
    congr 1
    funext o
    cases o <;> rfl
  by_cases hb : estimates.length ≠ k ∨ estimates.any Option.isNone
  · simp only [finishL, finish, List.length_map, hany, ite_eq_left hb,
      pointsOf, List.length_ofFn]
  · have hlen : estimates.length = k := by
      by_contra h
      exact hb (Or.inl h)
    let E := fun a : Fin k ↦
      (estimates[a.val]?.bind id).getD (⟨0, 1⟩ : Robust.Estimate d)
    have hs (i : Fin k) : ∃ v, estimates[i.val]'(by omega) = some v := by
      cases h : estimates[i.val]'(by omega) with
      | none =>
        exfalso
        apply hb
        right
        exact List.any_eq_true.mpr
          ⟨estimates[i.val], List.getElem_mem (by omega), by rw [h]; rfl⟩
      | some v => exact ⟨v, rfl⟩
    have hEs : (estimates.map (Option.map estimateList)).map (fun o ↦ o.getD ([], [])) =
        List.ofFn (fun a : Fin k ↦ estimateList (E a)) := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i hi hi'
        have hik : i < k := by simpa using hi'
        obtain ⟨v, hv⟩ := hs ⟨i, hik⟩
        simp only [List.getElem_map, List.getElem_ofFn]
        have hii : i < estimates.length := by omega
        rw [hv]
        simp only [Option.map_some, Option.getD_some, E,
          List.getElem?_eq_getElem hii, hv, Option.bind_some, Option.getD_some]
        rfl
    simp only [finishL, finish, List.length_map, hany, ite_eq_right hb]
    rw [hEs]
    simp only [List.map_ofFn, Function.comp_def, hlen, hT.agrees]
    exact recluster_agrees (fun a b ↦ T.tests mode Δ (E a) (E b) fuel) pts

private theorem finishL_polytime {α : Type} {enc : α ↪ List Bool}
    (T : TestCode) (hT : TestSpecL T) (mode : Mode)
    {d k fuel : α → ℕ} {Δ : α → ℚ} {pts : α → Points}
    {estimates : α → List (Option EstimateL)}
    (hd : ComputableInPolyTime d enc encUnary)
    (hk : ComputableInPolyTime k enc encNat)
    (hΔ : ComputableInPolyTime Δ enc Encoding.encRat)
    (hp : ComputableInPolyTime pts enc encPoints)
    (hf : ComputableInPolyTime fuel enc encUnary)
    (he : ComputableInPolyTime estimates enc (encList (encOption encEstimate))) :
    ComputableInPolyTime
      (fun a ↦ finishL T mode (d a) (k a) (Δ a) (pts a) (fuel a) (estimates a))
      enc encOutput := by
  have hEs : ComputableInPolyTime
      (fun a ↦ (estimates a).map fun E ↦ E.getD ([], [])) enc (encList encEstimate) :=
    mapWithInput he ((optionGetD encEstimate).comp ((snd _ _).prod (const ([], []))))
  have htests : ComputableInPolyTime
      (fun a ↦ ((estimates a).map fun E ↦ E.getD ([], [])).map fun A ↦
        ((estimates a).map fun E ↦ E.getD ([], [])).map fun B ↦
          T.run mode ((d a, Δ a, A, B), fuel a)) enc (encList (encList encTest)) := by
    apply mapWithInput hEs
    apply mapWithInput (hEs.comp (fst _ _))
    exact (hT.polytime mode).comp (by fun_prop)
  have hnone : ComputableInPolyTime
      (fun p : α × Option EstimateL ↦ p.2.isNone)
      (encPair enc (encOption encEstimate)) encBool := by
    refine (bool_not.comp (optionIsSome (snd _ _))).of_enc_eq fun p ↦ ?_
    dsimp only [Function.comp_apply]
    cases p.2 <;> rfl
  have hany := anyWithInput (test := fun _ E ↦ E.isNone) he hnone
  have hlen := (length_list (encOption encEstimate)).comp he
  unfold finishL
  apply FrameAux.Linear.ite_prop
  · apply decide_or
    · exact .of_tidy (ComputableTidilyInPolyTime.decide_ne
        (unary_to_binary.comp hlen).tidy hk.tidy)
    · simpa only [Bool.decide_coe] using hany
  · exact replicate ((length_list _).comp hp) (const 0)
  · exact recluster_polytime.comp
      ((hd.prod (((length_list _).comp hEs).prod htests)).prod hp)

/-- The binary k is compared with a stored list length, never expanded before that check. -/
theorem finish_polytime (T : TestCode) (hT : TestSpecL T) (mode : Mode) :
    ComputableInPolyTime
      (fun q : (ℕ × ℕ × ℚ × Points × List (Option EstimateL)) × ℕ ↦
        finishL T mode q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1 q.2 q.1.2.2.2.2)
      (encPair (encPair encUnary (encPair encNat (encPair Encoding.encRat
        (encPair encPoints (encList (encOption encEstimate)))))) encUnary) encOutput := by
  exact finishL_polytime T hT mode (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop)

end ABBKS26.Assembly.Exec
