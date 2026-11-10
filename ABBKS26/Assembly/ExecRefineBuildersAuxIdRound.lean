module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecRound

/-! Canonical degree-dependent moment rounding with a unary enumeration cap. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdRound

open Common MvPolynomial
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open SoS.Solver (RawPoly encRawPoly)

def run (d r fuel p b : ℕ) (q : RawPoly) : RawPoly :=
  (SoS.Mono.allB fuel d r).map fun μ ↦
    (μ, SpecRound.coefficient p b (SoS.Poly.coeff d q μ))

theorem run_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d r fuel p b : α → ℕ} {q : α → RawPoly}
    (hd : ComputableInPolyTime d enc encUnary)
    (hr : ComputableInPolyTime r enc encUnary)
    (hf : ComputableInPolyTime fuel enc encUnary)
    (hp : ComputableInPolyTime p enc encUnary)
    (hb : ComputableInPolyTime b enc encUnary)
    (hq : ComputableInPolyTime q enc encRawPoly) :
    ComputableInPolyTime (fun a ↦ run (d a) (r a) (fuel a) (p a) (b a) (q a))
      enc encRawPoly := by
  apply mapWithInput (MomentExpansion.allB_polytime.comp (hf.prod (hd.prod hr)))
  apply ComputableInPolyTime.prod (snd _ _)
  exact SpecRound.coefficient_polytime_of (hp.comp (fst _ _)) (hb.comp (fst _ _))
    (SoS.Poly.coeff' (hd.comp (fst _ _)) (hq.comp (fst _ _)) (snd _ _))

theorem length_run (d r fuel p b : ℕ) (q : RawPoly)
    (hr : r ≤ fuel) (hf : (d + 1) ^ r ≤ fuel) :
    (run d r fuel p b q).length ≤ (d + 1) ^ r := by
  simpa only [run, List.length_map, SoS.Mono.allB_eq hr hf] using SoS.Mono.length_all_le d r

theorem term_bounds (d r fuel p b : ℕ) (q : RawPoly)
    (hr : r ≤ fuel) (hf : (d + 1) ^ r ≤ fuel) (t : List ℕ × ℚ)
    (ht : t ∈ run d r fuel p b q) :
    t.1.length = d ∧ t.1.sum ≤ r ∧
      (encRat t.2).length ≤ 3 * (b + 1 + p) + 6 := by
  obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp ht
  rw [SoS.Mono.allB_eq hr hf] at hμ
  exact ⟨(SoS.Mono.mem_all.mp hμ).1, (SoS.Mono.mem_all.mp hμ).2,
    SpecRound.coefficient_bits p b _⟩


private theorem expo_self {d : ℕ} {μ : List ℕ} (hμ : μ.length = d) :
    SoS.Poly.expo d μ = μ := by
  apply List.ext_getElem (by simp [hμ])
  intro i hi hi'
  simp [SoS.Poly.expo, List.getD_eq_getElem?_getD, hi']

private theorem roundPoly_coeff {d : ℕ} (p : ℕ) (q : QPoly d) (α : Fin d →₀ ℕ) :
    (roundPoly p q).coeff α = roundRat p (q.coeff α) := by
  classical
  simp only [roundPoly, coeff_sum, coeff_monomial]
  by_cases hα : α ∈ q.support
  · simp [hα]
  · simp [hα, notMem_support_iff.mp hα, roundRat]

/-- Canonicalization sums duplicate terms before rounding, so cancellation and term order
do not affect the high-degree payload. -/
theorem run_agrees {d r : ℕ} (fuel p b : ℕ) (q : RawPoly)
    (hr : r ≤ fuel) (hf : (d + 1) ^ r ≤ fuel)
    (hq : (q.toPoly d).IsHomogeneous r)
    (hb : ∀ α, |(q.toPoly d).coeff α| ≤ 2 ^ b) :
    (run d r fuel p b q).toPoly d = roundPoly p (q.toPoly d) := by
  classical
  ext α
  rw [SoS.Poly.toPoly_eq_sum, run, List.map_map]
  rw [← List.sum_toFinset _ (by rw [SoS.Mono.allB_eq hr hf]; exact SoS.Mono.nodup_all d r)]
  simp only [Function.comp_apply, coeff_sum, coeff_monomial]
  have he (μ : List ℕ) (hμ : μ ∈ (SoS.Mono.allB fuel d r).toFinset) :
      SoS.Mono.toFinsupp d (SoS.Poly.expo d μ) = α ↔ μ = List.ofFn α := by
    have hlen := (SoS.Mono.mem_all.mp (SoS.Mono.allB_eq hr hf ▸ List.mem_toFinset.mp hμ)).1
    rw [expo_self hlen]
    constructor
    · intro h
      apply SoS.Mono.toFinsupp_inj hlen (by simp)
      simpa only [SoS.Poly.toFinsupp_ofFn] using h
    · rintro rfl
      exact SoS.Poly.toFinsupp_ofFn α
  have hsum : (∑ μ ∈ (SoS.Mono.allB fuel d r).toFinset,
      if SoS.Mono.toFinsupp d (SoS.Poly.expo d μ) = α then
        SpecRound.coefficient p b (SoS.Poly.coeff d q μ) else 0) =
      ∑ μ ∈ (SoS.Mono.allB fuel d r).toFinset,
        if μ = List.ofFn α then SpecRound.coefficient p b (SoS.Poly.coeff d q μ) else 0 := by
    apply Finset.sum_congr rfl
    intro μ hμ
    simp only [he μ hμ]
  rw [hsum, roundPoly_coeff]
  by_cases hm : List.ofFn α ∈ (SoS.Mono.allB fuel d r).toFinset
  · simp only [Finset.sum_ite_eq', hm, ite_true]
    rw [← SoS.Poly.coeff_toPoly q (by simp), SoS.Poly.toFinsupp_ofFn]
    exact ite_eq_left (hb α)
  · have hz : (q.toPoly d).coeff α = 0 := by
      by_contra hne
      have hd : (List.ofFn α).sum = r := by
        rw [← SoS.Mono.degree_toFinsupp (n := d) (e := List.ofFn α) (by simp),
          SoS.Poly.toFinsupp_ofFn,
          Finsupp.degree_eq_weight_one]
        exact hq hne
      apply hm
      rw [List.mem_toFinset, SoS.Mono.allB_eq hr hf, SoS.Mono.mem_all]
      exact ⟨by simp, by omega⟩
    simp [hm, hz, roundRat]

end ABBKS26.Assembly.Exec.RefineSynth.IdRound
