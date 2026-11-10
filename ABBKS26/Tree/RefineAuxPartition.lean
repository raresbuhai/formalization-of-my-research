module

public import ABBKS26.Tree.Split

/-!
# Partition bookkeeping for refinement

Splitting one block and its component set preserves the two partitions.
-/

@[expose] public section

namespace ABBKS26.Tree.RefineAux

noncomputable section

open Common

variable {n k d : ℕ}

def splitList {α : Type*} (S : List α) (j : ℕ) (L R : α) : List α :=
  S.take j ++ [L, R] ++ S.drop (j + 1)

theorem mem_splitList {α : Type*} (S : List α) (j : ℕ) (L R a : α)
    (ha : a ∈ splitList S j L R) : a = L ∨ a = R ∨ a ∈ S := by
  simp only [splitList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (ha | (ha | ha)) | ha
  · exact Or.inr (Or.inr (List.mem_of_mem_take ha))
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (List.mem_of_mem_drop ha))

theorem pairwise_splitList {α : Type*} [DecidableEq α]
    (S : List (Finset α)) (j : Fin S.length) (L R : Finset α)
    (hS : S.Pairwise Disjoint) (hLR : Disjoint L R) (hu : L ∪ R = S[j]) :
    (splitList S j L R).Pairwise Disjoint := by
  induction S with
  | nil => exact Fin.elim0 j
  | cons A S ih =>
    obtain ⟨hA, hS⟩ := List.pairwise_cons.mp hS
    cases j using Fin.cases with
    | zero =>
      change L ∪ R = A at hu
      have hL : L ⊆ A := hu ▸ Finset.subset_union_left
      have hR : R ⊆ A := hu ▸ Finset.subset_union_right
      change (L :: R :: S).Pairwise Disjoint
      refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, hS⟩⟩
      · intro B hB
        rcases List.mem_cons.mp hB with rfl | hB
        · exact hLR
        · exact (hA B hB).mono_left hL
      · intro B hB
        exact (hA B hB).mono_left hR
    | succ j =>
      change L ∪ R = S[j] at hu
      change (A :: splitList S j L R).Pairwise Disjoint
      refine List.pairwise_cons.mpr ⟨?_, ih j hS hu⟩
      intro B hB
      have hL : L ⊆ S[j] := hu ▸ Finset.subset_union_left
      have hR : R ⊆ S[j] := hu ▸ Finset.subset_union_right
      rcases mem_splitList S j L R B hB with rfl | rfl | hB
      · exact (hA S[j] (List.getElem_mem j.isLt)).mono_right hL
      · exact (hA S[j] (List.getElem_mem j.isLt)).mono_right hR
      · exact hA B hB

theorem union_splitList {α : Type*} [DecidableEq α]
    (S : List (Finset α)) (j : Fin S.length) (L R : Finset α)
    (hu : L ∪ R = S[j]) :
    (splitList S j L R).toFinset.biUnion id = S.toFinset.biUnion id := by
  induction S with
  | nil => exact Fin.elim0 j
  | cons A S ih =>
    cases j using Fin.cases with
    | zero =>
      change (L :: R :: S).toFinset.biUnion id = (A :: S).toFinset.biUnion id
      change L ∪ R = A at hu
      simp only [List.toFinset_cons, Finset.biUnion_insert, id_eq]
      rw [← Finset.union_assoc, hu]
    | succ j =>
      change L ∪ R = S[j] at hu
      change (A :: splitList S j L R).toFinset.biUnion id =
        (A :: S).toFinset.biUnion id
      simp only [List.toFinset_cons, Finset.biUnion_insert, id_eq, ih j hu]

theorem forall₂_splitList {α β : Type*} (P Q : α → β → Prop)
    (S : List α) (T : List β) (j : ℕ) (L R : α) (J K : β)
    (hST : List.Forall₂ P S T) (hmono : ∀ a b, P a b → Q a b)
    (hL : Q L J) (hR : Q R K) :
    List.Forall₂ Q (splitList S j L R) (splitList T j J K) := by
  apply List.rel_append
  · apply List.rel_append
    · exact List.Forall₂.imp hmono (List.forall₂_take j hST)
    · exact List.Forall₂.cons hL (List.Forall₂.cons hR List.Forall₂.nil)
  · exact List.Forall₂.imp hmono (List.forall₂_drop (j + 1) hST)

private theorem pairwise_iff_disjoint_get {α : Type*}
    (S : List (Finset α)) :
    S.Pairwise Disjoint ↔ ∀ a b : Fin S.length, a ≠ b → Disjoint S[a] S[b] := by
  rw [List.pairwise_iff_get]
  constructor
  · intro h a b hab
    rcases lt_or_gt_of_ne hab with hab | hab
    · exact h a b hab
    · exact (h b a hab).symm
  · intro h a b hab
    exact h a b hab.ne

private theorem union_ofFn {α : Type*} [DecidableEq α] {m : ℕ}
    (I : Fin m → Finset α) :
    (List.ofFn I).toFinset.biUnion id = Finset.univ.biUnion I := by
  ext x
  simp

theorem goodPartition_iff (ω : Fin n → ABBKS26.Triple k d) (w Φ : ℝ)
    (S : List (Finset (Fin n))) :
    GoodPartition ω w Φ S ↔
      S.Pairwise Disjoint ∧ S.toFinset.biUnion id = Finset.univ ∧
      ∃ T : List (Finset (Fin k)), T.Pairwise Disjoint ∧
        T.toFinset.biUnion id = Finset.univ ∧
        List.Forall₂ (fun N I ↦ I.Nonempty ∧ leakage ω N I ≤ Φ ∧ w * n / 4 ≤ N.card)
          S T := by
  classical
  constructor
  · rintro ⟨⟨hS, hc⟩, I, hI, hd, hu, hb⟩
    refine ⟨(pairwise_iff_disjoint_get S).mpr hS, hc, List.ofFn I, ?_, ?_, ?_⟩
    · rw [List.pairwise_iff_get]
      intro a b hab
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      apply hd
      intro he
      have hev : a.val = b.val := by simpa only [Fin.mk.injEq] using he
      exact hab.ne (Fin.ext hev)
    · rwa [union_ofFn]
    · apply List.forall₂_of_length_eq_of_get (by simp)
      intro i hi hi'
      simpa using And.intro (hI ⟨i, hi⟩) (hb ⟨i, hi⟩)
  · rintro ⟨hS, hc, T, hd, hu, hb⟩
    let I : Fin S.length → Finset (Fin k) := fun a ↦ T[a.val]'(hb.length_eq ▸ a.isLt)
    have hTI : List.ofFn I = T := by
      apply List.ext_getElem
      · simpa using hb.length_eq
      · intro i hi hi'
        simp [I]
    refine ⟨⟨(pairwise_iff_disjoint_get S).mp hS, hc⟩, I, ?_, ?_, ?_, ?_⟩
    · intro a
      exact (hb.get a.isLt (hb.length_eq ▸ a.isLt)).1
    · intro a b hab
      rw [← hTI] at hd
      have hh := (pairwise_iff_disjoint_get _).mp hd
      have hab' : (⟨a.val, by simp⟩ : Fin (List.ofFn I).length) ≠ ⟨b.val, by simp⟩ := by
        intro he
        have hev : a.val = b.val := by simpa only [Fin.mk.injEq] using he
        exact hab (Fin.ext hev)
      simpa using hh _ _ hab'
    · rw [← union_ofFn, hTI]
      exact hu
    · intro a
      exact (hb.get a.isLt (hb.length_eq ▸ a.isLt)).2

/-- Replace a block and its component set by matching disjoint pairs. -/
theorem goodPartition_split
    (ω : Fin n → ABBKS26.Triple k d) (w Φ Ψ : ℝ) (S : List (Finset (Fin n)))
    (I : Fin S.length → Finset (Fin k)) (hS : WeakPartition S)
    (hI : ∀ a, (I a).Nonempty) (hd : ∀ a b, a ≠ b → Disjoint (I a) (I b))
    (hu : Finset.univ.biUnion I = Finset.univ)
    (hb : ∀ a, leakage ω S[a] (I a) ≤ Φ ∧ w * n / 4 ≤ S[a].card)
    (j : Fin S.length) (A B : Finset (Fin n)) (L R : Finset (Fin k))
    (hAB : Disjoint A B) (hABu : A ∪ B = S[j])
    (hL : L.Nonempty) (hR : R.Nonempty) (hLR : Disjoint L R) (hLRu : L ∪ R = I j)
    (hΦ : Φ ≤ Ψ) (hl : leakage ω A L ≤ Ψ) (hr : leakage ω B R ≤ Ψ)
    (hA : w * n / 4 ≤ A.card) (hB : w * n / 4 ≤ B.card) :
    GoodPartition ω w Ψ (splitList S j A B) := by
  classical
  let T := List.ofFn I
  have hT : T.Pairwise Disjoint := by
    rw [List.pairwise_iff_get]
    intro a b hab
    simp only [T, List.get_eq_getElem, List.getElem_ofFn]
    apply hd
    intro he
    have hev : a.val = b.val := by simpa only [Fin.mk.injEq] using he
    exact hab.ne (Fin.ext hev)
  have hST : List.Forall₂
      (fun N J ↦ J.Nonempty ∧ leakage ω N J ≤ Φ ∧ w * n / 4 ≤ N.card) S T := by
    apply List.forall₂_of_length_eq_of_get (by simp [T])
    intro a ha ha'
    simpa [T] using And.intro (hI ⟨a, ha⟩) (hb ⟨a, ha⟩)
  let jT : Fin T.length := ⟨j.val, by simp [T]⟩
  have hju : L ∪ R = T[jT] := by simpa [T, jT] using hLRu
  apply (goodPartition_iff ω w Ψ _).mpr
  refine ⟨pairwise_splitList S j A B ((pairwise_iff_disjoint_get S).mpr hS.1) hAB hABu,
    (union_splitList S j A B hABu).trans hS.2, splitList T j L R, ?_, ?_, ?_⟩
  · exact pairwise_splitList T jT L R hT hLR hju
  · rw [union_splitList T jT L R hju, union_ofFn]
    exact hu
  · exact forall₂_splitList _ _ S T j A B L R hST
      (fun _ _ h ↦ ⟨h.1, h.2.1.trans hΦ, h.2.2⟩) ⟨hL, hl, hA⟩ ⟨hR, hr, hB⟩

end

end ABBKS26.Tree.RefineAux
