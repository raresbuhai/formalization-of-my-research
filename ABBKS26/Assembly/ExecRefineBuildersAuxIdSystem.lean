module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdPayload
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdNested

/-! A rational list program for SUB's plain constraint system, including zero removal. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdSystem

open Common MvPolynomial
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open SoS.Solver (RawPoly encRawPoly)

/-- One harmless zero term makes the capped Cartesian product valid for zero inputs. -/
def power (d fuel s : ℕ) (p : RawPoly) : RawPoly :=
  SoS.Poly.prodRaw d fuel (List.replicate s (p ++ NestedProgram.constant 0))

theorem power_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d fuel s : α → ℕ} {p : α → RawPoly}
    (hd : ComputableInPolyTime d enc encUnary)
    (hf : ComputableInPolyTime fuel enc encUnary)
    (hs : ComputableInPolyTime s enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly) :
    ComputableInPolyTime (fun a ↦ power (d a) (fuel a) (s a) (p a)) enc encRawPoly :=
  SoS.Poly.prodRaw' hd hf (replicate hs (listAppend' hp (const _)))

def alpha (s : ℕ) : ℚ :=
  ((List.range s).map fun j : ℕ ↦ 2 * (j : ℚ) + 1).prod

theorem alpha_polytime : ComputableInPolyTime alpha encUnary encRat := by
  apply rat_prod'
  apply mapWithInput range
  exact rat_add' (rat_mul' (const 2) (rat_natCast'
    (unary_to_binary.comp (snd encUnary encUnary)))) (const 1)

def deviation (d fuel s : ℕ) (moments : ℕ → RawPoly) : RawPoly :=
  moments (2 * s) ++ NestedProgram.scale (-alpha s) (power d fuel s (moments 2))

def constraint (d fuel s : ℕ) (ε : ℚ) (moments : ℕ → RawPoly) : RawPoly :=
  NestedProgram.scale ε (power d fuel (2 * s) (MomentProgram.normSq d)) ++
    NestedProgram.scale (-1) (SoS.Coords.mulRaw d
      (deviation d fuel s moments) (deviation d fuel s moments))

theorem deviation_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d fuel s : α → ℕ} {moments : α → ℕ → RawPoly}
    (hd : ComputableInPolyTime d enc encUnary)
    (hf : ComputableInPolyTime fuel enc encUnary)
    (hs : ComputableInPolyTime s enc encUnary)
    (hm : ComputableInPolyTime (fun a : α × ℕ ↦ moments a.1 a.2)
      (encPair enc encUnary) encRawPoly) :
    ComputableInPolyTime (fun a ↦ deviation (d a) (fuel a) (s a) (moments a))
      enc encRawPoly :=
  listAppend' (hm.comp (id'.prod (unary_mul' (const 2) hs)))
    (NestedProgram.scale_polytime (rat_neg' (alpha_polytime.comp hs))
      (power_polytime_of hd hf hs (hm.comp (id'.prod (const 2)))))

theorem constraint_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d fuel s : α → ℕ} {ε : α → ℚ} {moments : α → ℕ → RawPoly}
    (hd : ComputableInPolyTime d enc encUnary)
    (hf : ComputableInPolyTime fuel enc encUnary)
    (hs : ComputableInPolyTime s enc encUnary)
    (he : ComputableInPolyTime ε enc encRat)
    (hm : ComputableInPolyTime (fun a : α × ℕ ↦ moments a.1 a.2)
      (encPair enc encUnary) encRawPoly) :
    ComputableInPolyTime (fun a ↦ constraint (d a) (fuel a) (s a) (ε a) (moments a))
      enc encRawPoly := by
  have hdev := deviation_polytime_of hd hf hs hm
  exact listAppend'
    (NestedProgram.scale_polytime he (power_polytime_of hd hf
      (unary_mul' (const 2) hs) (SpecPoly.normSq_polytime_of hd)))
    (NestedProgram.scale_polytime (const (-1)) (SoS.PolyTime.mulRaw' hd hdev hdev))

def nonzero (d : ℕ) (p : RawPoly) : Bool := decide (NestedProgram.clean d p ≠ [])

theorem nonzero_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {p : α → RawPoly}
    (hd : ComputableInPolyTime d enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly) :
    ComputableInPolyTime (fun a ↦ nonzero (d a) (p a)) enc encBool := by
  have hc := NestedProgram.clean_polytime.comp (hd.prod hp)
  have hn := (length_list (encPair (encList encNat) encRat)).comp hc
  exact (bool_not.comp (unary_le' hn (const 0))).of_enc_eq fun a ↦ by
    simp [nonzero]

def run (d t fuel : ℕ) (ε : ℚ) (moments : ℕ → RawPoly) : List RawPoly :=
  [NestedProgram.constant 1 ++ NestedProgram.scale (-1) (MomentProgram.normSq d)] ++
    ((List.range (2 * t - 1)).map fun j ↦ constraint d fuel (j + 2) ε moments).filter
      (nonzero d)

theorem run_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d t fuel : α → ℕ} {ε : α → ℚ} {moments : α → ℕ → RawPoly}
    (hd : ComputableInPolyTime d enc encUnary)
    (ht : ComputableInPolyTime t enc encUnary)
    (hf : ComputableInPolyTime fuel enc encUnary)
    (he : ComputableInPolyTime ε enc encRat)
    (hm : ComputableInPolyTime (fun a : α × ℕ ↦ moments a.1 a.2)
      (encPair enc encUnary) encRawPoly) :
    ComputableInPolyTime (fun a ↦ run (d a) (t a) (fuel a) (ε a) (moments a))
      enc (encList encRawPoly) := by
  have hm' : ComputableInPolyTime
      (fun a : (α × ℕ) × ℕ ↦ moments a.1.1 a.2)
      (encPair (encPair enc encUnary) encUnary) encRawPoly :=
    hm.comp (((fst enc encUnary).comp (fst _ _)).prod (snd _ _))
  have hc : ComputableInPolyTime (fun a : α ↦
      (List.range (2 * t a - 1)).map fun j ↦
        constraint (d a) (fuel a) (j + 2) (ε a) (moments a))
      enc (encList encRawPoly) := mapWithInput
    (range.comp (unary_sub' (unary_mul' (const 2) ht) (const 1)))
    (constraint_polytime_of (hd.comp (fst _ _)) (hf.comp (fst _ _))
      (unary_add' (snd _ _) (const 2)) (he.comp (fst _ _))
      (moments := fun a : α × ℕ ↦ moments a.1) hm')
  exact listAppend'
    (cons' (listAppend' (const _) (NestedProgram.scale_polytime (const (-1))
      (SpecPoly.normSq_polytime_of hd))) (const []))
    (filterWithInput hc (nonzero_polytime_of (hd.comp (fst _ _)) (snd _ _)))

theorem length_run (d t fuel : ℕ) (ε : ℚ) (moments : ℕ → RawPoly) :
    (run d t fuel ε moments).length ≤ 2 * t + 1 := by
  have hb := List.length_filter_le (nonzero d)
    ((List.range (2 * t - 1)).map fun j ↦ constraint d fuel (j + 2) ε moments)
  simp only [run, List.length_append, List.length_singleton, List.length_map,
    List.length_range] at *
  omega

noncomputable section

theorem power_agrees (d fuel s : ℕ) (p : RawPoly)
    (hf : (p.length + 1) ^ s ≤ fuel) :
    (power d fuel s p).toPoly d = p.toPoly d ^ s := by
  unfold power
  rw [SoS.Poly.toPoly_prodRaw]
  · simp only [List.map_replicate, SoS.Poly.toPoly_append,
      NestedProgram.constant_toPoly, map_zero, add_zero, List.prod_replicate]
  · intro f hf
    rw [(List.mem_replicate.mp hf).2]
    simp [NestedProgram.constant]
  · simpa only [List.map_replicate, List.prod_replicate, List.length_append,
      NestedProgram.constant, List.length_singleton] using hf

theorem alpha_cast (s : ℕ) : (alpha s : ℝ) = IdCov.alpha s := by
  induction s with
  | zero => norm_num [alpha, IdCov.alpha]
  | succ s ih =>
    have hrec : (Nat.doubleFactorial (2 * (s + 1) - 1) : ℝ) =
        (2 * s + 1) * Nat.doubleFactorial (2 * s - 1) := by
      rw [show 2 * (s + 1) - 1 = 2 * s + 1 by omega, Nat.doubleFactorial_add_one]
      push_cast
      ring
    have ha : alpha (s + 1) = alpha s * (2 * (s : ℚ) + 1) := by
      simp [alpha, List.range_succ]
    rw [ha, Rat.cast_mul, ih]
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]
    change _ = (Nat.doubleFactorial (2 * (s + 1) - 1) : ℝ)
    rw [hrec]
    unfold IdCov.alpha
    ring

theorem deviation_agrees (d fuel s : ℕ) (moments : ℕ → RawPoly)
    (hf : ((moments 2).length + 1) ^ s ≤ fuel) :
    SoS.toReal ((deviation d fuel s moments).toPoly d) =
      IdCov.dev (fun q ↦ SoS.toReal ((moments q).toPoly d)) s := by
  simp only [deviation, SoS.Poly.toPoly_append, NestedProgram.scale_toPoly,
    power_agrees d fuel s _ hf, SoS.toReal, map_add, map_mul, map_pow, map_C,
    eq_ratCast, alpha_cast, map_neg, IdCov.dev]
  ring

theorem constraint_agrees (d fuel s : ℕ) (ε : ℚ) (moments : ℕ → RawPoly)
    (hf : ((moments 2).length + 1) ^ s ≤ fuel)
    (hn : (d + 1) ^ (2 * s) ≤ fuel) :
    SoS.toReal ((constraint d fuel s ε moments).toPoly d) =
      IdCov.constraint (fun q ↦ SoS.toReal ((moments q).toPoly d)) ε s := by
  have hpow := power_agrees d fuel (2 * s) (MomentProgram.normSq d)
    (by simpa [MomentProgram.normSq] using hn)
  rw [constraint, SoS.Poly.toPoly_append, NestedProgram.scale_toPoly,
    NestedProgram.scale_toPoly, SoS.Coords.toPoly_mulRaw, hpow,
    MomentProgram.normSq_toPoly]
  simp only [SoS.toReal, map_add, map_mul, map_C, map_pow, map_sum, map_X,
    map_neg, map_one, neg_one_mul]
  change C (ε : ℝ) * nsq ^ (2 * s) +
    -(SoS.toReal ((deviation d fuel s moments).toPoly d) *
      SoS.toReal ((deviation d fuel s moments).toPoly d)) = _
  rw [deviation_agrees d fuel s moments hf]
  rw [IdCov.constraint, pow_two, sub_eq_add_neg]
  rfl

theorem nonzero_agrees (d : ℕ) (p : RawPoly) :
    nonzero d p = true ↔ SoS.toReal (p.toPoly d) ≠ 0 := by
  classical
  have hz : NestedProgram.clean d p = [] ↔ p.toPoly d = 0 := by
    constructor
    · intro h
      rw [← NestedProgram.clean_toPoly d p, h]
      simp [SoS.Solver.RawPoly.toPoly]
    · intro h
      simp only [NestedProgram.clean, List.map_eq_nil_iff, List.filter_eq_nil_iff]
      intro t _
      have hc := congrArg (fun q : QPoly d ↦ q.coeff
        (SoS.Mono.toFinsupp d (SoS.Poly.expo d t.1))) h
      rw [SoS.Poly.coeff_toPoly p (SoS.Poly.length_expo d t.1)] at hc
      have hz : SoS.Poly.coeff d p (SoS.Poly.expo d t.1) = 0 := by simpa using hc
      simp [hz]
  simp only [nonzero, decide_eq_true_eq, ne_eq, hz, SoS.toReal]
  apply not_congr
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact (MvPolynomial.map_injective (algebraMap ℚ ℝ)
      (algebraMap ℚ ℝ).injective) (h.trans (map_zero _).symm)

theorem system_congr {d : ℕ} (t : ℕ) (ε : ℝ) (M N : ℕ → RPoly d)
    (hM : ∀ s, 1 ≤ s → s ≤ 2 * t → M (2 * s) = N (2 * s)) (ht : 1 ≤ t) :
    IdCov.system M t ε = IdCov.system N t ε := by
  unfold IdCov.system
  congr 1
  congr 1
  apply List.map_congr_left
  intro j hj
  have hs : 1 ≤ j + 2 ∧ j + 2 ≤ 2 * t := by
    have := List.mem_range.mp hj
    omega
  simp only [IdCov.constraint, IdCov.dev, hM (j + 2) hs.1 hs.2,
    show M 2 = N 2 from hM 1 le_rfl (by omega)]

private theorem filter_decode (d : ℕ) (l : List RawPoly) :
    (l.filter (nonzero d)).map (fun p ↦ SoS.toReal (p.toPoly d)) =
      (l.map (fun p ↦ SoS.toReal (p.toPoly d))).filter (fun p ↦ p ≠ 0) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have ht : nonzero d p = decide (SoS.toReal (p.toPoly d) ≠ 0) := by
      apply Bool.eq_iff_iff.mpr
      rw [nonzero_agrees, decide_eq_true_eq]
    by_cases hz : SoS.toReal (p.toPoly d) = 0
    · simp [ht, hz, ih]
    · simp [ht, hz, ih]

/-- Raw filtering deletes exactly the zero constraints omitted by the analytic SUB
system. No empirical predicate or target-dependent filtering occurs. -/
theorem run_agrees (d t fuel : ℕ) (ε : ℚ) (moments : ℕ → RawPoly)
    (hf : ∀ s, 2 ≤ s → s ≤ 2 * t → ((moments 2).length + 1) ^ s ≤ fuel)
    (hn : ∀ s, 2 ≤ s → s ≤ 2 * t → (d + 1) ^ (2 * s) ≤ fuel) :
    (run d t fuel ε moments).map (fun p ↦ SoS.toReal (p.toPoly d)) =
      IdCov.system (fun q ↦ SoS.toReal ((moments q).toPoly d)) t ε := by
  rw [run, List.map_append, List.map_singleton]
  have hsphere : SoS.toReal ((NestedProgram.constant 1 ++
      NestedProgram.scale (-1) (MomentProgram.normSq d)).toPoly d) = 1 - nsq := by
    simp [SoS.Poly.toPoly_append, NestedProgram.constant_toPoly,
      NestedProgram.scale_toPoly, MomentProgram.normSq_toPoly, SoS.toReal, nsq,
      sub_eq_add_neg]
  rw [hsphere]
  congr 1
  rw [filter_decode, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hs : 2 ≤ j + 2 ∧ j + 2 ≤ 2 * t := by
    have := List.mem_range.mp hj
    omega
  exact constraint_agrees d fuel (j + 2) ε moments
    (hf _ hs.1 hs.2) (hn _ hs.1 hs.2)

end

end ABBKS26.Assembly.Exec.RefineSynth.IdSystem
