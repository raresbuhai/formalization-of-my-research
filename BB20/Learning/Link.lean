module

public import BB20.Learning.Algorithm

/-!
# The algorithm's empirical proxy and the empirical proxy of a sample

The algorithm computes `ν̂` from the samples as lists of bits, with variables as numbers
(`BB20.empNuL`); the analysis works with `BB20.empNu` on `Fin n`. They agree
(`BB20.Learning.empNuL_eq`) on the samples `sampleList X` of `X : Fin M → Config n`.

`BB20.Learning.Accurate` states that an empirical proxy is close to `ν` on the sets the algorithm
looks at.
-/

@[expose] public section

namespace BB20.Learning

open Finset

variable {n m : ℕ}

/-- The variables among `A` below `n`, as elements of `Fin n`. -/
def toFin (n : ℕ) (A : Finset ℕ) : Finset (Fin n) := univ.filter fun i ↦ (i : ℕ) ∈ A

@[simp]
theorem mem_toFin {A : Finset ℕ} {i : Fin n} : i ∈ toFin n A ↔ (i : ℕ) ∈ A := by
  simp [toFin]

theorem toFin_map (B : Finset (Fin n)) : toFin n (B.map Fin.valEmbedding) = B := by
  ext i
  simp [Fin.val_inj]

theorem map_toFin {A : Finset ℕ} (hA : ∀ a ∈ A, a < n) :
    (toFin n A).map Fin.valEmbedding = A := by
  ext a
  simp only [mem_map, mem_toFin, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro ha
    exact ⟨⟨a, hA a ha⟩, ha, rfl⟩

theorem toFin_insert_map (u : Fin n) (B : Finset (Fin n)) :
    toFin n (insert (u : ℕ) (B.map Fin.valEmbedding)) = insert u B := by
  ext i
  simp [Fin.val_inj]

theorem toFin_union_map (B C : Finset (Fin n)) :
    toFin n (B.map Fin.valEmbedding ∪ C.map Fin.valEmbedding) = B ∪ C := by
  ext i
  simp [Fin.val_inj]

theorem toFin_insert_union_map (u : Fin n) (B C : Finset (Fin n)) :
    toFin n (insert (u : ℕ) (B.map Fin.valEmbedding ∪ C.map Fin.valEmbedding)) =
      insert u (B ∪ C) := by
  ext i
  simp [Fin.val_inj]

theorem bitAt_sampleList {M : ℕ} (X : Fin M → Config n) {k i : ℕ} (hk : k < M) (hi : i < n) :
    bitAt (sampleList X) k i = X ⟨k, hk⟩ ⟨i, hi⟩ := by
  simp [bitAt, sampleList, hk, hi]

theorem length_sampleList {M : ℕ} (X : Fin M → Config n) : (sampleList X).length = M := by
  simp [sampleList]

theorem empMargL_eq {M : ℕ} (X : Fin M → Config n) (A : Finset ℕ) (z : Config n) :
    (empMargL (sampleList X) n A z : ℝ) = empMarg X (toFin n A) z := by
  set P : ℕ → Prop := fun k ↦ ∀ i ∈ A, ∀ h : i < n, bitAt (sampleList X) k i = z ⟨i, h⟩ with hP
  have h1 : (List.range M).countP (fun k ↦ decide (P k)) = ((Finset.range M).filter P).card := by
    rw [List.countP_eq_length_filter]
    rfl
  have h2 : (univ.filter fun k : Fin M ↦ ∀ i ∈ toFin n A, X k i = z i).card =
      ((Finset.range M).filter P).card := by
    rw [← card_map Fin.valEmbedding]
    congr 1
    ext k
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range, hP]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨i.2, fun a ha h ↦ ?_⟩
      exact (bitAt_sampleList X i.2 h).trans (hi ⟨a, h⟩ (by simpa using ha))
    · rintro ⟨hk, hp⟩
      refine ⟨⟨k, hk⟩, fun j hj ↦ ?_, rfl⟩
      exact (bitAt_sampleList X hk j.2).symm.trans (hp j (mem_toFin.1 hj) j.2)
  unfold empMargL empMarg
  rw [length_sampleList, h1, ← h2]
  push_cast
  rfl

theorem empNuL_eq {M : ℕ} (X : Fin M → Config n) (u : Fin n) (I S : Finset (Fin n)) :
    (empNuL (sampleList X) n u (I.map Fin.valEmbedding) (S.map Fin.valEmbedding) : ℝ) =
      empNu X u I S := by
  unfold empNuL empNu
  push_cast
  rw [card_map]
  congr 1
  refine sum_congr rfl fun z _ ↦ ?_
  rw [empMargL_eq, empMargL_eq, empMargL_eq, empMargL_eq, toFin_insert_union_map,
    toFin_insert_map, toFin_union_map, toFin_map]

/-- The empirical proxy `nh` (with variables as numbers) is within `ε` of `ν` on the pairs
`(I, S)` the algorithm can look at at `u`: disjoint, without `u`, with `|I| ≤ k` and `|S| ≤ L`. -/
def Accurate (R : RBM n m) (u : Fin n) (nh : Finset ℕ → Finset ℕ → ℚ) (k : ℕ) (L ε : ℝ) :
    Prop :=
  ∀ I S : Finset (Fin n), u ∉ I → u ∉ S → Disjoint I S → I.card ≤ k → (S.card : ℝ) ≤ L →
    |(nh (I.map Fin.valEmbedding) (S.map Fin.valEmbedding) : ℝ) - R.nu u I S| ≤ ε

end BB20.Learning
