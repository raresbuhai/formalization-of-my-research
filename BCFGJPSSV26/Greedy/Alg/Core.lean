module

public import BCFGJPSSV26.Greedy.Alg.Merge
public import BCFGJPSSV26.Greedy.LMP
public import Complexity.Foundations.Data.List.EraseDups

/-!
# The core theorem

[BCFGJPSSV26a, Theorem 5.16] on a core input (`BCFGJPSSV26.Greedy.core_spec`): for good constants
and a core input whose distances lie in `[1, M]` with `2 ≤ n` and `1 ≤ k < min (n, m)`, the core
outputs at most `k + 6R` distinct facilities, of cost at most `(ρ + 10δ) cost(O)` for every
nonempty set `O` of at most `k` facilities.

The proof: the merge ends with a good output (`BCFGJPSSV26.Greedy.Ctx.merge_spec`), to which the
robust LMP guarantee (`BCFGJPSSV26.Greedy.robust_lmp`) applies. With exactly `k` regular atoms
the opening costs cancel; with fewer (only at `f̂ = δ`) the extra `k δ ≤ δ cost(O)`, since every
distance is at least `1`. The slack `k n η ≤ δ² / 100` is at most `δ²/100 · cost(O)`. Replacing
free copies by their originals does not raise the cost.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Ctx

variable {C : Ctx} {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)
include hX

omit hX in
/-- The output of a good solution is a list of distinct facilities, nonempty, of length at most
the number of atoms. -/
theorem toCenters_spec (_hX : C.Hyp X) {H : List (List AAtom)} (hok : C.SolOK H)
    (hreg : 1 ≤ nRegA H) :
    toCenters H ≠ [] ∧ (toCenters H).Nodup ∧ (∀ i ∈ toCenters H, i < C.ip.m) ∧
      (toCenters H).length ≤ H.flatten.length := by
  have hmem : ∀ i, i ∈ toCenters H ↔ ∃ a ∈ H.flatten, a.1 = i := by
    intro i
    simp only [toCenters, List.mem_eraseDups, List.mem_map]
  refine ⟨fun h ↦ ?_, List.nodup_eraseDups _, fun i hi ↦ ?_, ?_⟩
  · obtain ⟨a, ha⟩ : ∃ a, a ∈ H.flatten := by
      unfold nRegA at hreg
      obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos hreg
      exact ⟨a, List.mem_of_mem_filter ha⟩
    have := (hmem a.1).2 ⟨a, ha, rfl⟩
    rw [h] at this
    exact List.not_mem_nil this
  · obtain ⟨a, ha, rfl⟩ := (hmem i).1 hi
    exact (hok a ha).1
  · refine (List.eraseDups_sublist _).length_le.trans ?_
    rw [List.length_map]

omit hX in
/-- A solution with at most three free atoms per sequence has at most `nReg + 6R` atoms. -/
theorem flatten_length_le (_hX : C.Hyp X) {H : List (List AAtom)}
    (hlen : H.length = 2 * C.ip.R) (hfree : ∀ q, nFreeSeqA (H.getD q []) ≤ 3) :
    H.flatten.length ≤ nRegA H + 6 * C.ip.R := by
  have hfree' : ∀ S ∈ H, nFreeSeqA S ≤ 3 := by
    intro S hS
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hS
    have := hfree q
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some] at this
  have key : ∀ H' : List (List AAtom), (∀ S ∈ H', nFreeSeqA S ≤ 3) →
      (H'.flatten.filter fun a ↦ !(a.2 == 0)).length ≤ 3 * H'.length := by
    intro H' h
    induction H' with
    | nil => simp
    | cons S H' ih =>
      rw [List.flatten_cons, List.filter_append, List.length_append, List.length_cons]
      have h1 := h S List.mem_cons_self
      have h2 := ih fun S' hS' ↦ h S' (List.mem_cons_of_mem _ hS')
      unfold nFreeSeqA at h1
      have e : (S.filter fun a ↦ !(a.2 == 0)) = S.filter fun a ↦ a.2 != 0 := rfl
      rw [e]
      omega
  have h1 := List.length_eq_length_filter_add (l := H.flatten) fun a ↦ a.2 == 0
  have h2 := key H hfree'
  unfold nRegA
  omega

/-- **Free copies replaced by their originals**: the cost of the output is at most the
connection cost of the solution. -/
theorem coreCost_toCenters_le {f η : ℚ} {H : List (List AAtom)}
    (hH : Sol C.par X.d f η (decH hX H)) (hok : C.SolOK H) :
    coreCost (C.ip.n, C.ip.m, C.ip.k, C.tab) (toCenters H) ≤ connCost C.par X.d (decH hX H) := by
  unfold coreCost connCost
  rw [list_sum_map_range, Finset.sum_range]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  have hlt := Sol.profL_lt_K hX.good hH j
  obtain ⟨p, hp, hpeq⟩ := exists_profF_eq C.par.K X.d hlt
  rw [decH_flatten] at hp hpeq
  simp only [pairs, decS, List.map_map, List.mem_toFinset, List.mem_map] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  have ham := (hok a ha).1
  have hpeq' : profL C.par.K X.d (decH hX H).flatten j = X.d j ⟨a.1, ham⟩ + C.aoff a := by
    rw [decH_flatten]
    simpa [profL, Function.comp_apply, decA_pair hX ham] using hpeq
  rw [hpeq']
  have hK := hX.K_pos
  have h0 := aoff_nonneg hK.le a
  have hin : C.dist j a.1 ∈ (toCenters H).map fun i ↦ (C.tab.getD j []).getD i 0 := by
    refine List.mem_map.2 ⟨a.1, ?_, rfl⟩
    simp only [toCenters, List.mem_eraseDups, List.mem_map]
    exact ⟨a, ha, rfl⟩
  have hmin := (Combine.minQ_spec (List.ne_nil_of_mem hin)).2 _ hin
  have hd : C.dist j a.1 = X.d j ⟨a.1, ham⟩ := hX.dist_eq j ⟨a.1, ham⟩
  change Combine.minQ ((toCenters H).map fun i ↦ (C.tab.getD j []).getD i 0) ≤ _
  linarith

omit hX in
/-- Every set of facilities costs at least `n` when all distances are at least `1`. -/
theorem costF_ge {X : Space C.ip.n C.ip.m} (hd1 : ∀ j i, 1 ≤ X.d j i) {O : Finset (Fin C.ip.m)}
    (hO : O.Nonempty) : (C.ip.n : ℚ) ≤ costF X.d O := by
  unfold costF
  simp only [hO, dite_true]
  have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦
    (Finset.le_inf' hO (X.d j) fun i _ ↦ hd1 j i : (1 : ℚ) ≤ O.inf' hO (X.d j))
  simpa using h

end Ctx

/-- The slack: `s n η ≤ δ² / 100` for `η = δ² / (100 n²)` and `s ≤ n`. -/
theorem eta_bound {n s δ : ℚ} (hn : 0 < n) (hs : s ≤ n) :
    s * n * (δ ^ 2 / (100 * n ^ 2)) ≤ δ ^ 2 / 100 := by
  have h : s * n * (δ ^ 2 / (100 * n ^ 2)) = s / n * (δ ^ 2 / 100) := by
    field_simp
  rw [h]
  have : s / n ≤ 1 := by rw [div_le_one hn]; exact hs
  have : 0 ≤ δ ^ 2 / 100 := by positivity
  nlinarith

/-- The arithmetic of the core theorem: from the robust LMP guarantee with `s` regular atoms,
`|O| = o` and opening cost `f`, the connection cost `A` is at most `(ρ + 10 δ) B`. -/
theorem core_ineq {δ A B s k n η f o : ℚ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 100) (hB : n ≤ B)
    (hn1 : 1 ≤ n) (hkn : k ≤ n) (hs : s ≤ k) (hs0 : 0 ≤ s) (hη : s * n * η ≤ δ ^ 2 / 100)
    (hopen : o * f ≤ s * f + k * δ)
    (hlmp : (1 - δ) * A + s * f ≤ (ρ + 6 * δ) * B + o * f + s * n * η) :
    A ≤ (ρ + 10 * δ) * B := by
  have hρ := one_le_ρ
  have hρ' : ρ ≤ 2 := by rw [ρ_eq]; norm_num
  have hn0 : 0 ≤ n := hs0.trans (hs.trans hkn)
  have hB1 : 0 ≤ B := hn0.trans hB
  have h1 : k * δ ≤ δ * B := by nlinarith
  have hn1 : 1 ≤ n ∨ n < 1 := le_or_gt 1 n
  have h2 : (1 - δ) * A ≤ (ρ + 7 * δ) * B + δ ^ 2 / 100 := by nlinarith
  have h3 : δ ^ 2 / 100 ≤ δ ^ 2 / 100 * B := by nlinarith [sq_nonneg δ]
  have h4 : (ρ + 7 * δ) * B + δ ^ 2 / 100 * B ≤ (1 - δ) * ((ρ + 10 * δ) * B) := by
    have : ρ + 7 * δ + δ ^ 2 / 100 ≤ (1 - δ) * (ρ + 10 * δ) := by nlinarith
    nlinarith
  have h5 : (1 - δ) * A ≤ (1 - δ) * ((ρ + 10 * δ) * B) := by linarith
  exact le_of_mul_le_mul_left h5 (by linarith)

/-- **The core theorem.** -/
theorem core_spec {c : Consts} (hc : c.Good) {x : CoreIn} {X : Space x.1 x.2.1}
    (hx : CoreOK c x X) :
    core c x ≠ [] ∧ (core c x).Nodup ∧ (∀ i ∈ core c x, i < x.2.1) ∧
      (core c x).length ≤ x.2.2.1 + 6 * Rof c x.1 ∧
      ∀ O : Finset (Fin x.2.1), O.Nonempty → O.card ≤ x.2.2.1 →
        coreCost x (core c x) ≤ (ρ + 10 * c.δ) * costF X.d O := by
  have hX : (ctx c x).Hyp X := hyp_ctx hc hx
  obtain ⟨hsol, hok, -, hfree3, hcount, hreg⟩ := Ctx.merge_spec hX
  obtain ⟨hne, hnd, hlt, hlen⟩ := Ctx.toCenters_spec hX hok hreg
  have hlen1 : (ctx c x).merge.1.length = 2 * (ctx c x).ip.R := by
    have h := hsol.1
    simp only [Ctx.decH, List.length_map] at h
    exact h
  have hlen2 := Ctx.flatten_length_le hX hlen1 hfree3
  have hRk : nRegA (ctx c x).merge.1 ≤ x.2.2.1 := by
    rcases hcount with h | ⟨h, -⟩
    · exact h.le
    · exact h
  have hnR : nRegA (ctx c x).merge.1 = nReg (Ctx.decH hX (ctx c x).merge.1) :=
    Ctx.nRegA_eq hX _
  refine ⟨hne, hnd, hlt, ?_, fun O hO hOk ↦ ?_⟩
  · change (toCenters (ctx c x).merge.1).length ≤ _
    have : (ctx c x).ip.R = Rof c x.1 := rfl
    omega
  -- the cost
  have hcost := Ctx.coreCost_toCenters_le hX hsol hok
  have hf := Ctx.nη_lt_fhat hX (ctx c x).merge.2
  have hlmp := robust_lmp X (ctx c x).par hX.good hX.d1 hf hsol O hO
  have hnR' : @nReg x.2.1 (Ctx.decH hX (ctx c x).merge.1) = nRegA (ctx c x).merge.1 := hnR.symm
  rw [hnR'] at hlmp
  have hB : (x.1 : ℚ) ≤ @costF x.1 x.2.1 X.d O := Ctx.costF_ge (C := ctx c x) hX.d1 hO
  have eδ : (ctx c x).ip.δ = c.δ := rfl
  have en : (ctx c x).ip.n = x.1 := rfl
  have ek : (ctx c x).ip.k = x.2.2.1 := rfl
  have ePδ : (ctx c x).par.δ = c.δ := rfl
  have ePη : (ctx c x).par.η = (ctx c x).ip.η := rfl
  rw [ePδ, ePη] at hlmp
  have hf' : (x.1 : ℚ) * (ctx c x).ip.η < (ctx c x).fhat (ctx c x).merge.2 := hf
  have hf0 : 0 ≤ (ctx c x).fhat (ctx c x).merge.2 := by
    have : (0 : ℚ) ≤ x.1 * (ctx c x).ip.η :=
      mul_nonneg (Nat.cast_nonneg _) (hX.good.η_nonneg)
    linarith [hf']
  have hη : (nRegA (ctx c x).merge.1 : ℚ) * x.1 * (ctx c x).ip.η ≤ c.δ ^ 2 / 100 := by
    rw [hX.η_eq, eδ, en]
    exact eta_bound (by exact_mod_cast (by have := hx.two_le_n; omega : 0 < x.1))
      (by exact_mod_cast (hRk.trans hx.k_lt_n.le))
  have hopen : (O.card : ℚ) * (ctx c x).fhat (ctx c x).merge.2 ≤
      nRegA (ctx c x).merge.1 * (ctx c x).fhat (ctx c x).merge.2 + x.2.2.1 * c.δ := by
    rcases hcount with h | ⟨-, hb, -⟩
    · rw [h, ek]
      have : (O.card : ℚ) ≤ x.2.2.1 := by exact_mod_cast hOk
      have : (0 : ℚ) ≤ x.2.2.1 * c.δ := mul_nonneg (Nat.cast_nonneg _) hc.δ_pos.le
      nlinarith
    · rw [hb, Ctx.fhat_zero hX, eδ]
      have : (O.card : ℚ) ≤ x.2.2.1 := by exact_mod_cast hOk
      nlinarith [Nat.cast_nonneg (α := ℚ) (nRegA (ctx c x).merge.1), hc.δ_pos]
  exact hcost.trans (core_ineq hc.δ_pos hc.δ_le hB
    (by exact_mod_cast (by have := hx.two_le_n; omega : 1 ≤ x.1))
    (by exact_mod_cast hx.k_lt_n.le)
    (by exact_mod_cast hRk) (Nat.cast_nonneg _) hη hopen hlmp)

end BCFGJPSSV26.Greedy
