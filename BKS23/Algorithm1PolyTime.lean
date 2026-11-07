module

public import BKS23.Algorithm1
public import BKS23.AlgorithmPolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-!
# The algorithm of Theorem 5.6 (1) runs in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for the functions of
`BKS23.Algorithm.run1`, as in `BKS23/AlgorithmPolyTime.lean`, ending with
`BKS23.Algorithm.exists_alg1_inO`.

The cleanup threshold `Δ = ⌊k² / (n (log₂ n + 1))⌋ + 1` is computed in binary, since it may be
exponential in the length of `k`; so is the cleanup with it (`BKS23.Algorithm.cleanupL_binary`).
-/

@[expose] public section

namespace BKS23.Algorithm

open Turing.MultiTapeTM ComputableInPolyTime
open SoS SoS.Solver SoS.Poly SoS.PolyTime

variable {α : Type} {input : α ↪ List Bool}

/-! ### The refinement -/

theorem adjL_polytime : ComputableInPolyTime (fun x : List (ℕ × ℕ) × ℕ × ℕ ↦ adjL x.1 x.2.1 x.2.2)
    (encPair encE2 (encPair encUnary encUnary)) encBool := by
  unfold adjL
  exact bool_and' (bool_and' (bool_not.comp (unary_beq' (by fun_prop) (by fun_prop)))
    (bool_not.comp (decide_mem (by fun_prop) (by fun_prop))))
    (bool_not.comp (decide_mem (by fun_prop) (by fun_prop)))

@[fun_prop]
theorem adjL' {f : α → List (ℕ × ℕ)} {g h : α → ℕ} (hf : ComputableInPolyTime f input encE2)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encUnary) :
    ComputableInPolyTime (fun a ↦ adjL (f a) (g a) (h a)) input encBool :=
  adjL_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem nbrCount_polytime : ComputableInPolyTime
    (fun x : List (ℕ × ℕ) × List ℕ × ℕ ↦ nbrCount x.1 x.2.1 x.2.2)
    (encPair encE2 (encPair encVs encUnary)) encUnary := by
  unfold nbrCount
  exact countPWithInput (by fun_prop) (by fun_prop)

@[fun_prop]
theorem nbrCount' {f : α → List (ℕ × ℕ)} {g : α → List ℕ} {h : α → ℕ}
    (hf : ComputableInPolyTime f input encE2) (hg : ComputableInPolyTime g input encVs)
    (hh : ComputableInPolyTime h input encUnary) :
    ComputableInPolyTime (fun a ↦ nbrCount (f a) (g a) (h a)) input encUnary :=
  nbrCount_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem refineSet_polytime : ComputableInPolyTime
    (fun x : ℕ × List (ℕ × ℕ) × List ℕ × ℕ ↦ refineSet x.1 x.2.1 x.2.2.1 x.2.2.2)
    (encPair encUnary (encPair encE2 (encPair encVs encUnary))) encVs := by
  unfold refineSet
  exact filterWithInput (by fun_prop) (unary_le' (by fun_prop) (by fun_prop))

@[fun_prop]
theorem refineSet' {f : α → ℕ} {g : α → List (ℕ × ℕ)} {h : α → List ℕ} {l : α → ℕ}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encE2)
    (hh : ComputableInPolyTime h input encVs) (hl : ComputableInPolyTime l input encUnary) :
    ComputableInPolyTime (fun a ↦ refineSet (f a) (g a) (h a) (l a)) input encVs :=
  refineSet_polytime.comp (g := fun a ↦ (f a, g a, h a, l a)) (hf.prod (hg.prod (hh.prod hl)))

theorem candidates1_polytime : ComputableInPolyTime
    (fun x : ℕ × List (ℕ × ℕ) × RawPoly ↦ candidates1 x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encE2 encRaw)) (encList encVs) := by
  unfold candidates1
  exact flatMapWithInput (by fun_prop) (mapWithInput (by fun_prop) (by fun_prop))

@[fun_prop]
theorem candidates1' {f : α → ℕ} {g : α → List (ℕ × ℕ)} {h : α → RawPoly}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encE2)
    (hh : ComputableInPolyTime h input encRaw) :
    ComputableInPolyTime (fun a ↦ candidates1 (f a) (g a) (h a)) input (encList encVs) :=
  candidates1_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

/-! ### The threshold -/

theorem delta1_polytime : ComputableInPolyTime (fun x : ℕ × ℕ ↦ delta1 x.1 x.2)
    (encPair encUnary encNat) encNat := by
  unfold delta1
  have hlog : ComputableInPolyTime (fun x : ℕ × ℕ ↦ Nat.log 2 x.1) (encPair encUnary encNat)
      encUnary :=
    binary_log_two.comp (toBinary' (fst _ _))
  have hd : ComputableInPolyTime (fun x : ℕ × ℕ ↦ x.1 * (Nat.log 2 x.1 + 1))
      (encPair encUnary encNat) encNat :=
    toBinary' (unary_mul' (fst _ _) (unary_add' hlog (const 1)))
  have hq : ComputableInPolyTime (fun x : ℕ × ℕ ↦ x.2 * x.2 / (x.1 * (Nat.log 2 x.1 + 1)))
      (encPair encUnary encNat) encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_div' (binary_mul' (snd _ _) (snd _ _)).tidy hd.tidy)
  exact binary_add.comp (g := fun x : ℕ × ℕ ↦ (x.2 * x.2 / (x.1 * (Nat.log 2 x.1 + 1)), 1))
    (hq.prod (const 1))

@[fun_prop]
theorem delta1' {f g : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ delta1 (f a) (g a)) input encNat :=
  delta1_polytime.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

/-! ### The cleanup, with a binary threshold -/

theorem pruneStep_binary_polytime : ComputableInPolyTime
    (fun p : (ℕ × List (List ℕ)) × List ℕ ↦ pruneStep p.1.1 p.1.2 p.2)
    (encPair (encPair encNat (encList encVs)) encVs) (encList encVs) := by
  unfold pruneStep
  exact ite' (allWithInput (by fun_prop) (binary_lt' (toBinary' (by fun_prop)) (by fun_prop)))
    (by fun_prop) (by fun_prop)

/-- `BKS23.Algorithm.cleanupL` runs in polynomial time with the threshold in binary. -/
theorem cleanupL_binary : ComputableInPolyTime
    (fun x : ℕ × ℕ × List (ℕ × ℕ) × List (List ℕ) ↦ cleanupL x.1 x.2.1 x.2.2.1 x.2.2.2)
    (encPair encNat (encPair encNat (encPair encE2 (encList encVs)))) (encList encVs) := by
  have h := funext fun x : ℕ × ℕ × List (ℕ × ℕ) × List (List ℕ) ↦
    cleanupL_eq x.1 x.2.1 x.2.2.1 x.2.2.2
  rw [h]
  set enc := encPair encNat (encPair encNat (encPair encE2 (encList encVs)))
  have hl : ComputableInPolyTime (fun x : ℕ × ℕ × List (ℕ × ℕ) × List (List ℕ) ↦
      x.2.2.2.filter (isCliqueL x.1 x.2.2.1)) enc (encList encVs) :=
    filterWithInput (by fun_prop) (by fun_prop)
  refine foldlWith_of_bounded_growth (par := fun x : ℕ × ℕ × List (ℕ × ℕ) × List (List ℕ) ↦ x.2.1)
    (by fun_prop) hl (const []) pruneStep_binary_polytime
    (growth := fun x ↦ 2 * (enc x).length + 1) ?_ ?_
  · exact ((PolyBounded.const 2).mul PolyBounded.self).add (.const 1)
  · intro x state value hv
    have hv' : value ∈ x.2.2.2 := (List.mem_filter.1 hv).1
    have h1 : (encVs value).length ≤ (enc x).length := by
      refine (SizedListEncoding.length_elem_le (encA := encVs) (encL := encList encVs) _ _
        hv').trans ?_
      simp only [enc, length_encPair]
      omega
    unfold pruneStep
    split_ifs
    · rw [length_encList_append_singleton]
      omega
    · omega

theorem cleanupL_binary' {f g : α → ℕ} {h : α → List (ℕ × ℕ)} {l : α → List (List ℕ)}
    (hf : ComputableInPolyTime f input encNat) (hg : ComputableInPolyTime g input encNat)
    (hh : ComputableInPolyTime h input encE2) (hl : ComputableInPolyTime l input (encList encVs)) :
    ComputableInPolyTime (fun a ↦ cleanupL (f a) (g a) (h a) (l a)) input (encList encVs) :=
  cleanupL_binary.comp (g := fun a ↦ (f a, g a, h a, l a)) (hf.prod (hg.prod (hh.prod hl)))

/-! ### The algorithm -/

/-- **The algorithm of Theorem 5.6 (1) runs in polynomial time** in the input and the budget `L`,
in unary. The middle component, unused, makes the pipeline that of `BKS23.Algorithm.run`. -/
theorem run1_polytime : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ ↦ run1 (p.1.1, p.2))
    (encPair (encPair encInput encUnary) encUnary) encOutput := by
  set enc := encPair (encPair encInput encUnary) encUnary
  have hn : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ ↦ numV p.1.1) enc encUnary :=
    numV_polytime.comp (g := fun p : (Input × ℕ) × ℕ ↦ p.1.1) (by fun_prop)
  have hb : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ ↦ p.1.1.2.2) enc encBits := by fun_prop
  have hk : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ ↦ p.1.1.2.1) enc encNat := by fun_prop
  have hout : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ ↦
      SoS.Core.core (solverInput p.1.1 0, p.2)) enc encRaw :=
    core_run_polytime.comp (g := fun p : (Input × ℕ) × ℕ ↦ ((p.1.1, 0), p.2))
      ((((fst _ _).comp (fst _ _)).prod (const 0)).prod (snd _ _))
  exact toBinaryLists.comp (cleanupL_binary' hk (delta1' hn hk) (nonEdges' hn hb)
    (candidates1' hn (nonEdges' hn hb) hout))

/-- **The algorithm of Theorem 5.6 (1) runs in polynomial time**: within
`c ((|x| + 2)^d + |(x, r)|)` steps and cells. The coins are read but not used. -/
theorem exists_alg1_inO : ∃ d c : ℕ,
    ComputableInTimeAndSpace alg1 (encPair encInput encBits) encOutput
      (fun xr ↦ c * (((encInput xr.1).length + 2) ^ d + (encPair encInput encBits xr).length))
      (fun xr ↦ c * (((encInput xr.1).length + 2) ^ d + (encPair encInput encBits xr).length)) := by
  obtain ⟨dP, eP, hP⟩ := problem_polytime.tidy.exists_degree
  obtain ⟨cP, hcP⟩ := hP.2
  obtain ⟨K, D, hbud⟩ := exists_budget_inO
  obtain ⟨dr, er, hr⟩ := run1_polytime.tidy.exists_degree
  set G := max dP (max D dr) with hG
  refine ⟨8 * (eP + 1) * G * (0 + 1), ?_⟩
  set encXR := encPair encInput encBits
  -- The pipeline: `(x, 0)`, the problem, the budget, and the algorithm.
  have h1 : ComputableTidilyInO (fun xr : Input × List Bool ↦ (xr.1, 0)) encXR
      (encPair encInput encUnary) (fun xr ↦ (encXR xr).length + (encXR xr).length)
      (fun xr ↦ (encXR xr).length + (encXR xr).length) :=
    (ComputableTidilyInO.fst encInput encBits).prod (ComputableTidilyInO.const 0)
  have h2 := hP.inO.comp h1
  have h3 := hbud.comp h2
  have h4 := h1.prod h3
  have h5 := hr.inO.comp h4
  obtain ⟨c, hc, -⟩ := h5.computableInO
  -- The algorithm is this pipeline.
  replace hc : ComputableInTimeAndSpace alg1 encXR encOutput _ _ := hc
  -- The bounds.
  refine ⟨c * (5 + (1 + K + 3 ^ dr) * (cP * (2 * 0 + 2) ^ eP + 2 * 0 + 8) ^ ((8 * 0 + 8) * G)),
    hc.mono (fun xr ↦ ?_) (fun xr ↦ ?_)⟩
  all_goals
    have hR : 2 * (encInput xr.1).length + 1 ≤ (encXR xr).length := by
      simp only [encXR, length_encPair]
      omega
    have hPl := hcP (xr.1, 0)
    simp only [length_encPair_input_unary] at hPl
    have hdeg : (solverInput xr.1 0).1.degree = 8 * 0 + 6 := rfl
    refine pad_arith (t := 0) hG hR hPl (le_of_eq ?_)
    simp only [Function.comp_apply, padMeasure, hdeg, length_encPair, encUnary_apply,
      List.length_replicate]

end BKS23.Algorithm
