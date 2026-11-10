module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecMoments

/-! Canonical quartic payloads with fixed dyadic coefficient bounds. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecRound

open Common MvPolynomial
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open SoS.Solver (RawPoly encRawPoly)

/-- The enumeration has polynomial size even on malformed polynomial inputs. -/
def monomials (d : ℕ) : List (List ℕ) := SoS.Mono.allB ((d + 1) ^ 4 + 4) d 4

theorem monomials_eq (d : ℕ) : monomials d = SoS.Mono.all d 4 := by
  exact SoS.Mono.allB_eq (by omega) (by omega)

theorem monomials_polytime :
    ComputableInPolyTime monomials encUnary (encList (encList encNat)) := by
  have hb : ComputableInPolyTime (fun d : ℕ ↦ (d + 1) ^ 4 + 4)
      encUnary encUnary := unary_add'
    ((unary_pow 4).comp (unary_add' id' (const 1))) (const 4)
  exact MomentExpansion.allB_polytime.comp (hb.prod (id'.prod (const 4)))

/-- A coefficient outside the certified magnitude range is replaced by zero. -/
def coefficient (p b : ℕ) (q : ℚ) : ℚ :=
  if |q| ≤ 2 ^ b then roundRat p q else 0

theorem coefficient_polytime_of {α : Type} {enc : α ↪ List Bool}
    {p b : α → ℕ} {q : α → ℚ}
    (hp : ComputableInPolyTime p enc encUnary)
    (hb : ComputableInPolyTime b enc encUnary)
    (hq : ComputableInPolyTime q enc encRat) :
    ComputableInPolyTime (fun a ↦ coefficient (p a) (b a) (q a)) enc encRat := by
  unfold coefficient
  exact ite_decide (rat_le' (rat_abs' hq) (rat_two_pow' hb))
    (FrameAux.roundRat_polytime hp hq) (const 0)


theorem coefficient_bits (p b : ℕ) (q : ℚ) :
    (encRat (coefficient p b q)).length ≤ 3 * (b + 1 + p) + 6 := by
  unfold coefficient
  split_ifs with h
  · exact (NestedProgram.rounded_coefficient p b q h).2
  · have hz := SoS.PolyTime.length_encRat_le_of_small (SoS.PolyTime.small_zero p (b + 1))
    exact hz

def run (d p b : ℕ) (q : RawPoly) : RawPoly :=
  (monomials d).map fun μ ↦ (μ, coefficient p b (SoS.Poly.coeff d q μ))

theorem run_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d p b : α → ℕ} {q : α → RawPoly}
    (hd : ComputableInPolyTime d enc encUnary)
    (hp : ComputableInPolyTime p enc encUnary)
    (hb : ComputableInPolyTime b enc encUnary)
    (hq : ComputableInPolyTime q enc encRawPoly) :
    ComputableInPolyTime (fun a ↦ run (d a) (p a) (b a) (q a)) enc encRawPoly := by
  apply mapWithInput (monomials_polytime.comp hd)
  apply ComputableInPolyTime.prod (snd _ _)
  exact coefficient_polytime_of (hp.comp (fst _ _)) (hb.comp (fst _ _))
    (SoS.Poly.coeff' (hd.comp (fst _ _)) (hq.comp (fst _ _)) (snd _ _))


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
theorem run_agrees {d : ℕ} (p b : ℕ) (q : RawPoly)
    (hq : (q.toPoly d).IsHomogeneous 4)
    (hb : ∀ α, |(q.toPoly d).coeff α| ≤ 2 ^ b) :
    (run d p b q).toPoly d = roundPoly p (q.toPoly d) := by
  classical
  ext α
  rw [SoS.Poly.toPoly_eq_sum, run, List.map_map]
  rw [← List.sum_toFinset _ (by rw [monomials_eq]; exact SoS.Mono.nodup_all d 4)]
  simp only [Function.comp_apply, coeff_sum, coeff_monomial]
  have he (μ : List ℕ) (hμ : μ ∈ (monomials d).toFinset) :
      SoS.Mono.toFinsupp d (SoS.Poly.expo d μ) = α ↔ μ = List.ofFn α := by
    have hlen := (SoS.Mono.mem_all.mp (monomials_eq d ▸ List.mem_toFinset.mp hμ)).1
    rw [expo_self hlen]
    constructor
    · intro h
      apply SoS.Mono.toFinsupp_inj hlen (by simp)
      simpa only [SoS.Poly.toFinsupp_ofFn] using h
    · rintro rfl
      exact SoS.Poly.toFinsupp_ofFn α
  have hsum : (∑ μ ∈ (monomials d).toFinset,
      if SoS.Mono.toFinsupp d (SoS.Poly.expo d μ) = α then
        coefficient p b (SoS.Poly.coeff d q μ) else 0) =
      ∑ μ ∈ (monomials d).toFinset,
        if μ = List.ofFn α then coefficient p b (SoS.Poly.coeff d q μ) else 0 := by
    apply Finset.sum_congr rfl
    intro μ hμ
    simp only [he μ hμ]
  rw [hsum, roundPoly_coeff]
  by_cases hm : List.ofFn α ∈ (monomials d).toFinset
  · simp only [Finset.sum_ite_eq', hm, ite_true]
    rw [← SoS.Poly.coeff_toPoly q (by simp), SoS.Poly.toFinsupp_ofFn]
    exact ite_eq_left (hb α)
  · have hz : (q.toPoly d).coeff α = 0 := by
      by_contra hne
      have hd : (List.ofFn α).sum = 4 := by
        rw [← SoS.Mono.degree_toFinsupp (n := d) (e := List.ofFn α) (by simp),
          SoS.Poly.toFinsupp_ofFn,
          Finsupp.degree_eq_weight_one]
        exact hq hne
      apply hm
      rw [List.mem_toFinset, monomials_eq, SoS.Mono.mem_all]
      exact ⟨by simp, by omega⟩
    simp [hm, hz, roundRat]

end ABBKS26.Assembly.Exec.RefineSynth.SpecRound
