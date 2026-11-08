module

public import BHJK25.RS.Decode.Sem

/-!
# The per-guess decoder: fraction-free elimination

`BHJK25.RS.DecodeAux.kernelVec` finds a nonzero vector supported on the allowed columns and
killed by every row, whenever one exists (`BHJK25.RS.DecodeAux.Sem.kernelVec_spec`).

The family `N` of `K = (W + 1)²` vectors (read in the field) keeps two invariants with respect to
the rows `R` processed so far: every member is supported on the allowed columns and killed by
every row of `R`, and every vector supported on the allowed columns and killed by every row of
`R` is a combination of the members. Initially the members are the allowed unit vectors (and
zero). A row `a` with values `bᵢ = a · Nᵢ`, all zero, keeps the family; otherwise with a pivot
`bⱼ ≠ 0` the members `bⱼ Nᵢ - bᵢ Nⱼ` are killed by `a`, and a combination `v = Σ cᵢ Nᵢ` killed by
`a` (so `Σ cᵢ bᵢ = 0`) is `Σ (cᵢ / bⱼ) (bⱼ Nᵢ - bᵢ Nⱼ)`. At the end, if a nonzero allowed vector is
killed by all rows, it is a combination of the members, so some member is nonzero, and the first
one is the output.
-/

@[expose] public section

namespace BHJK25.RS.DecodeAux

namespace Sem

variable {fl : List ℕ} {F : Type*} [Field F] (S : Sem fl F)

/-- The invariant of the elimination. -/
private def Inv (m W K : ℕ) (R : List (List (List ℕ))) (f : ℕ → ℕ → F) : Prop :=
  (∀ a ∈ R, ∀ i < K, ∑ k ∈ Finset.range K, S.ev (a.getD k []) * f i k = 0) ∧
  (∀ i < K, ∀ k < K, low m W k = false → f i k = 0) ∧
  ∀ v : ℕ → F, (∀ k < K, low m W k = false → v k = 0) →
    (∀ a ∈ R, ∑ k ∈ Finset.range K, S.ev (a.getD k []) * v k = 0) →
    ∃ c : ℕ → F, ∀ k < K, v k = ∑ i ∈ Finset.range K, c i * f i k

private theorem inv_congr {m W K : ℕ} {R : List (List (List ℕ))} {f g : ℕ → ℕ → F}
    (hfg : ∀ i < K, ∀ k < K, f i k = g i k) (hf : Inv S m W K R f) : Inv S m W K R g := by
  obtain ⟨hA, hB, hC⟩ := hf
  refine ⟨fun a ha i hi ↦ ?_, fun i hi k hk hl ↦ ?_, fun v hv hR ↦ ?_⟩
  · rw [← hA a ha i hi]
    exact Finset.sum_congr rfl fun k hk ↦ by rw [hfg i hi k (Finset.mem_range.mp hk)]
  · rw [← hfg i hi k hk]
    exact hB i hi k hk hl
  · obtain ⟨c, hc⟩ := hC v hv hR
    refine ⟨c, fun k hk ↦ ?_⟩
    rw [hc k hk]
    exact Finset.sum_congr rfl fun i hi ↦ by rw [hfg i (Finset.mem_range.mp hi) k hk]

/-- A row killing every member keeps the invariant. -/
private theorem inv_append_of_zero {m W K : ℕ} {R : List (List (List ℕ))} {f : ℕ → ℕ → F}
    (a : List (List ℕ)) (hf : Inv S m W K R f)
    (ha : ∀ i < K, ∑ k ∈ Finset.range K, S.ev (a.getD k []) * f i k = 0) :
    Inv S m W K (R ++ [a]) f := by
  obtain ⟨hA, hB, hC⟩ := hf
  refine ⟨fun r hr ↦ ?_, hB, fun v hv hR ↦ hC v hv fun r hr ↦ hR r (List.mem_append_left _ hr)⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact hA r hr
  · rw [List.mem_singleton.mp hr]
    exact ha

private theorem sum_mul_comb (K : ℕ) (r g h : ℕ → F) (x y : F) :
    ∑ k ∈ Finset.range K, r k * (x * g k - y * h k) =
      x * ∑ k ∈ Finset.range K, r k * g k - y * ∑ k ∈ Finset.range K, r k * h k := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- A pivot step keeps the invariant. -/
private theorem inv_append_of_pivot {m W K : ℕ} {R : List (List (List ℕ))} {f : ℕ → ℕ → F}
    (a : List (List ℕ)) (hf : Inv S m W K R f) {j : ℕ} (hj : j < K)
    (hbj : ∑ k ∈ Finset.range K, S.ev (a.getD k []) * f j k ≠ 0) :
    Inv S m W K (R ++ [a]) fun i k ↦
      (∑ k ∈ Finset.range K, S.ev (a.getD k []) * f j k) * f i k -
        (∑ k ∈ Finset.range K, S.ev (a.getD k []) * f i k) * f j k := by
  obtain ⟨hA, hB, hC⟩ := hf
  set b : ℕ → F := fun i ↦ ∑ k ∈ Finset.range K, S.ev (a.getD k []) * f i k with hb
  change b j ≠ 0 at hbj
  change Inv S m W K (R ++ [a]) fun i k ↦ b j * f i k - b i * f j k
  refine ⟨fun r hr i hi ↦ ?_, fun i hi k hk hl ↦ ?_, fun v hv hR ↦ ?_⟩
  · rw [sum_mul_comb]
    rcases List.mem_append.mp hr with hr | hr
    · rw [hA r hr i hi, hA r hr j hj, mul_zero, mul_zero, sub_zero]
    · rw [List.mem_singleton.mp hr]
      change b j * b i - b i * b j = 0
      ring
  · change b j * f i k - b i * f j k = 0
    rw [hB i hi k hk hl, hB j hj k hk hl, mul_zero, mul_zero, sub_zero]
  · obtain ⟨c, hc⟩ := hC v hv fun r hr ↦ hR r (List.mem_append_left _ hr)
    have hcb : ∑ i ∈ Finset.range K, c i * b i = 0 := by
      rw [← hR a (List.mem_append_right _ (List.mem_singleton_self a))]
      calc ∑ i ∈ Finset.range K, c i * b i
          = ∑ k ∈ Finset.range K, S.ev (a.getD k []) * ∑ i ∈ Finset.range K, c i * f i k := by
            simp only [hb, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
        _ = _ := Finset.sum_congr rfl fun k hk ↦ by rw [hc k (Finset.mem_range.mp hk)]
    refine ⟨fun i ↦ c i / b j, fun k hk ↦ ?_⟩
    have e : ∀ i, c i / b j * (b j * f i k - b i * f j k) =
        c i * f i k - c i * b i * (f j k / b j) := fun i ↦ by
      field_simp
    rw [Finset.sum_congr rfl fun i _ ↦ e i, Finset.sum_sub_distrib, ← Finset.sum_mul, hcb,
      zero_mul, sub_zero, hc k hk]

/-- The entries of the initial family. -/
private theorem ev_initFam (m W : ℕ) {i k : ℕ} (hi : i < (W + 1) * (W + 1))
    (hk : k < (W + 1) * (W + 1)) :
    S.ev (((initFam fl m W).getD i []).getD k []) =
      if i = k ∧ low m W k = true then 1 else 0 := by
  simp only [initFam, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    List.getElem?_range hk, Option.map_some, Option.getD_some]
  have e : ((i == k && low m W k) = true) ↔ (i = k ∧ low m W k = true) := by simp
  by_cases h : i = k ∧ low m W k = true
  · rw [ite_eq_left (e.mpr h), ite_eq_left h, S.ev_one]
  · rw [ite_eq_right (mt e.mp h), ite_eq_right h, S.ev_zero]

/-- The initial family satisfies the invariant. -/
private theorem inv_initFam (m W : ℕ) :
    Inv S m W ((W + 1) * (W + 1)) []
      fun i k ↦ S.ev (((initFam fl m W).getD i []).getD k []) := by
  refine ⟨fun a ha ↦ absurd ha List.not_mem_nil, fun i hi k hk hl ↦ ?_, fun v hv _ ↦ ?_⟩
  · beta_reduce
    rw [ev_initFam S m W hi hk, ite_eq_right fun h ↦ by rw [h.2] at hl; exact absurd hl (by simp)]
  · refine ⟨v, fun k hk ↦ ?_⟩
    beta_reduce
    rw [Finset.sum_eq_single k]
    · rw [ev_initFam S m W hk hk]
      by_cases hl : low m W k = true
      · rw [ite_eq_left ⟨rfl, hl⟩, mul_one]
      · rw [ite_eq_right fun h ↦ hl h.2, mul_zero, hv k hk (by simpa using hl)]
    · intro i hi hik
      rw [ev_initFam S m W (Finset.mem_range.mp hi) hk, ite_eq_right fun h ↦ hik h.1, mul_zero]
    · intro hk'
      exact absurd (Finset.mem_range.mpr hk) hk'

/-- The two cases of an elimination step: all row values vanish and the family is kept, or
there is a pivot. -/
private theorem elimStep_cases (K : ℕ) (N : List (List (List ℕ))) (a : List (List ℕ)) :
    ((∀ i < K, S.ev (dot fl K a (N.getD i [])) = 0) ∧ elimStep fl K N a = N) ∨
    ∃ j < K, S.ev (dot fl K a (N.getD j [])) ≠ 0 ∧ ∀ i < K, ∀ k < K,
      S.ev (((elimStep fl K N a).getD i []).getD k []) =
        S.ev (dot fl K a (N.getD j [])) * S.ev ((N.getD i []).getD k []) -
          S.ev (dot fl K a (N.getD i [])) * S.ev ((N.getD j []).getD k []) := by
  have hnil : isZ fl [] = true := (S.isZ_iff []).mpr S.ev_nil
  dsimp only [elimStep]
  cases hf : (List.range K).find? fun i ↦
      !isZ fl (((List.range K).map fun i ↦ dot fl K a (N.getD i [])).getD i []) with
  | none =>
    have hall : ∀ i < K,
        isZ fl (((List.range K).map fun i ↦ dot fl K a (N.getD i [])).getD i []) = true :=
      fun i hi ↦ by simpa using List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
    have h0 : isZ fl (((List.range K).map fun i ↦ dot fl K a (N.getD i [])).getD 0 []) = true := by
      rcases Nat.eq_zero_or_pos K with hK | hK
      · subst hK
        simpa using hnil
      · exact hall 0 hK
    left
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · rw [← getD_map_range_of_lt (fun i ↦ dot fl K a (N.getD i [])) [] hi]
      exact (S.isZ_iff _).mp (hall i hi)
    · rw [Option.getD_none, ite_eq_left h0]
  | some j =>
    obtain ⟨hp, hmem, -⟩ := List.find?_range_eq_some.mp hf
    have hj := List.mem_range.mp hmem
    have hz : isZ fl (((List.range K).map fun i ↦ dot fl K a (N.getD i [])).getD j []) = false := by
      simpa using hp
    right
    refine ⟨j, hj, ?_, fun i hi k hk ↦ ?_⟩
    · rw [← getD_map_range_of_lt (fun i ↦ dot fl K a (N.getD i [])) [] hj]
      exact (S.isZ_eq_false_iff _).mp hz
    · rw [Option.getD_some, ite_eq_right (by rw [hz]; exact Bool.false_ne_true)]
      simp only [getD_map_range_of_lt _ _ hi, getD_map_range_of_lt _ _ hk,
        getD_map_range_of_lt _ _ hj, S.ev_sub, S.ev_mul]

/-- An elimination step keeps the invariant. -/
private theorem inv_elimStep {m W K : ℕ} {R N : List (List (List ℕ))} (a : List (List ℕ))
    (hN : Inv S m W K R fun i k ↦ S.ev ((N.getD i []).getD k [])) :
    Inv S m W K (R ++ [a]) fun i k ↦ S.ev (((elimStep fl K N a).getD i []).getD k []) := by
  rcases elimStep_cases S K N a with ⟨hb, he⟩ | ⟨j, hj, hbj, he⟩
  · rw [he]
    refine inv_append_of_zero S a hN fun i hi ↦ ?_
    rw [← hb i hi, S.ev_dot]
  · rw [S.ev_dot] at hbj
    refine inv_congr S (fun i hi k hk ↦ ?_) (inv_append_of_pivot S a hN hj hbj)
    rw [he i hi k hk, S.ev_dot, S.ev_dot]

/-- Processing a list of rows keeps the invariant. -/
private theorem inv_foldl {m W K : ℕ} (rows : List (List (List ℕ))) :
    ∀ R N : List (List (List ℕ)), (Inv S m W K R fun i k ↦ S.ev ((N.getD i []).getD k [])) →
      Inv S m W K (R ++ rows) fun i k ↦
        S.ev (((rows.foldl (elimStep fl K) N).getD i []).getD k []) := by
  induction rows with
  | nil =>
    intro R N hN
    rwa [List.append_nil, List.foldl_nil]
  | cons r rs ih =>
    intro R N hN
    rw [List.foldl_cons, show R ++ r :: rs = R ++ [r] ++ rs by simp]
    exact ih _ _ (inv_elimStep S r hN)

/-- **The kernel vector.** If some vector supported on the allowed columns and nonzero on
`[0, K)`, `K = (W + 1)²`, is killed by every row, then so is the output of the elimination. -/
theorem kernelVec_spec (m W : ℕ) (rows : List (List (List ℕ)))
    (h : ∃ v : ℕ → F, (∀ k < (W + 1) * (W + 1), low m W k = false → v k = 0) ∧
      (∃ k < (W + 1) * (W + 1), v k ≠ 0) ∧
      ∀ a ∈ rows, ∑ k ∈ Finset.range ((W + 1) * (W + 1)), S.ev (a.getD k []) * v k = 0) :
    (∀ k < (W + 1) * (W + 1), low m W k = false →
      S.ev ((kernelVec fl ((W + 1) * (W + 1)) (initFam fl m W) rows).getD k []) = 0) ∧
    (∃ k < (W + 1) * (W + 1),
      S.ev ((kernelVec fl ((W + 1) * (W + 1)) (initFam fl m W) rows).getD k []) ≠ 0) ∧
    ∀ a ∈ rows, ∑ k ∈ Finset.range ((W + 1) * (W + 1)), S.ev (a.getD k []) *
      S.ev ((kernelVec fl ((W + 1) * (W + 1)) (initFam fl m W) rows).getD k []) = 0 := by
  obtain ⟨v, hv, ⟨k0, hk0, hvk0⟩, hvR⟩ := h
  set K := (W + 1) * (W + 1) with hK
  set N := rows.foldl (elimStep fl K) (initFam fl m W) with hN
  have hinv := inv_foldl S rows [] (initFam fl m W) (inv_initFam S m W)
  rw [List.nil_append, ← hK, ← hN] at hinv
  obtain ⟨hA, hB, hC⟩ := hinv
  obtain ⟨c, hc⟩ := hC v hv hvR
  have hne : ∃ i < K, ∃ k < K, S.ev ((N.getD i []).getD k []) ≠ 0 := by
    rw [hc k0 hk0] at hvk0
    obtain ⟨i, hi, hci⟩ := Finset.exists_ne_zero_of_sum_ne_zero hvk0
    exact ⟨i, Finset.mem_range.mp hi, k0, hk0, right_ne_zero_of_mul hci⟩
  have hkv : kernelVec fl K (initFam fl m W) rows = N.getD (((List.range K).find? fun i ↦
      (List.range K).any fun k ↦ !isZ fl ((N.getD i []).getD k [])).getD 0) [] := rfl
  obtain ⟨i0, hf⟩ : ∃ i0, (List.range K).find? (fun i ↦
      (List.range K).any fun k ↦ !isZ fl ((N.getD i []).getD k [])) = some i0 := by
    obtain ⟨i, hi, k, hk, hik⟩ := hne
    refine Option.ne_none_iff_exists'.mp fun hnone ↦ ?_
    refine List.find?_eq_none.mp hnone i (List.mem_range.mpr hi) (List.any_eq_true.mpr ?_)
    exact ⟨k, List.mem_range.mpr hk, by simpa using (S.isZ_eq_false_iff _).mpr hik⟩
  obtain ⟨hp, hmem, -⟩ := List.find?_range_eq_some.mp hf
  have hi0 := List.mem_range.mp hmem
  rw [hkv, hf, Option.getD_some]
  refine ⟨fun k hk hl ↦ hB i0 hi0 k hk hl, ?_, fun a ha ↦ hA a ha i0 hi0⟩
  obtain ⟨k, hk, hz⟩ := List.any_eq_true.mp hp
  exact ⟨k, List.mem_range.mp hk, (S.isZ_eq_false_iff _).mp (by simpa using hz)⟩

end Sem

end BHJK25.RS.DecodeAux
