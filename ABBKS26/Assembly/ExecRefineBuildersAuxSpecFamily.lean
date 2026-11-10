module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecPoly

/-! Rational list programs for the centered constraint family. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecFamily

open Common MvPolynomial
open Encoding (encRat)
open SoS.Solver (RawPoly encRawPoly)
open Turing.MultiTapeTM ComputableInPolyTime

/-- The first variable block is `u`, and the second is `v`. -/
def images (d : ℕ) (s t : ℚ) : List RawPoly :=
  (List.range d).map fun i ↦
    [(NestedProgram.unitExp (d + d) i 1, s),
      (NestedProgram.unitExp (d + d) (d + i) 1, t)]

def pull (d : ℕ) (p : RawPoly) (s t : ℚ) : RawPoly :=
  SpecPoly.substitute d (d + d) 4 16 p (images d s t)

def radial (d : ℕ) (s t : ℚ) : RawPoly :=
  pull d (MomentProgram.normSq d) s t

/-- Four times the polarization, so squaring requires no further scalar factors. -/
def hessian (d : ℕ) (p : RawPoly) : RawPoly :=
  NestedProgram.scale (1 / 3)
    (pull d p 1 1 ++ pull d p (-1) 1 ++
      NestedProgram.scale (-2) (pull d p 0 1) ++
      NestedProgram.scale (-2) (pull d p 1 0))

def qConstraint (d : ℕ) (p : RawPoly) (εq : ℚ) : RawPoly :=
  NestedProgram.scale (εq ^ 2) (MomentProgram.power d (MomentProgram.normSq d) 4) ++
    NestedProgram.scale (-1 / 9) (SoS.Coords.mulRaw d p p)

def hConstraint (d : ℕ) (p : RawPoly) (εh : ℚ) : RawPoly :=
  NestedProgram.scale εh
    (MomentProgram.power (d + d) (radial d 0 1) 4 ++
      MomentProgram.power (d + d) (radial d 1 0) 4) ++
    NestedProgram.scale (-1) (SoS.Coords.mulRaw (d + d) (hessian d p) (hessian d p))

def plain (d : ℕ) (p : RawPoly) (εq : ℚ) : List RawPoly :=
  [NestedProgram.constant 1 ++ NestedProgram.scale (-1) (MomentProgram.normSq d),
    qConstraint d p εq]

def family (d : ℕ) (p : RawPoly) (εq εh : ℚ) : Rounding.RawFamily :=
  ⟨d, plain d p εq, [hConstraint d p εh], [0]⟩

theorem images_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {s t : α → ℚ}
    (hd : ComputableInPolyTime d enc encUnary)
    (hs : ComputableInPolyTime s enc encRat)
    (ht : ComputableInPolyTime t enc encRat) :
    ComputableInPolyTime (fun a ↦ images (d a) (s a) (t a))
      enc (encList encRawPoly) := by
  unfold images
  apply mapWithInput (range.comp hd)
  apply cons'
  · exact (NestedProgram.unitExp_polytime
      (unary_add' (hd.comp (fst _ _)) (hd.comp (fst _ _))) (snd _ _) (const 1)).prod
        (hs.comp (fst _ _))
  · apply cons'
    · exact (NestedProgram.unitExp_polytime
        (unary_add' (hd.comp (fst _ _)) (hd.comp (fst _ _)))
        (unary_add' (hd.comp (fst _ _)) (snd _ _)) (const 1)).prod
          (ht.comp (fst _ _))
    · exact const []

theorem pull_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {p : α → RawPoly} {s t : α → ℚ}
    (hd : ComputableInPolyTime d enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly)
    (hs : ComputableInPolyTime s enc encRat)
    (ht : ComputableInPolyTime t enc encRat) :
    ComputableInPolyTime (fun a ↦ pull (d a) (p a) (s a) (t a)) enc encRawPoly :=
  SpecPoly.substitute_polytime_of hd (unary_add' hd hd) (const 4) (const 16)
    hp (images_polytime_of hd hs ht)

theorem hessian_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {p : α → RawPoly}
    (hd : ComputableInPolyTime d enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly) :
    ComputableInPolyTime (fun a ↦ hessian (d a) (p a)) enc encRawPoly := by
  unfold hessian
  apply NestedProgram.scale_polytime (const _)
  exact listAppend' (listAppend' (listAppend'
    (pull_polytime_of hd hp (const _) (const _))
    (pull_polytime_of hd hp (const _) (const _)))
    (NestedProgram.scale_polytime (const _)
      (pull_polytime_of hd hp (const _) (const _))))
    (NestedProgram.scale_polytime (const _)
      (pull_polytime_of hd hp (const _) (const _)))

theorem qConstraint_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {p : α → RawPoly} {εq : α → ℚ}
    (hd : ComputableInPolyTime d enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly)
    (hq : ComputableInPolyTime εq enc encRat) :
    ComputableInPolyTime (fun a ↦ qConstraint (d a) (p a) (εq a))
      enc encRawPoly := by
  unfold qConstraint
  exact listAppend'
    (NestedProgram.scale_polytime (FrameAux.Linear.rat_pow' hq (const 2))
      (SpecPoly.power_polytime_of 4 hd (SpecPoly.normSq_polytime_of hd)))
    (NestedProgram.scale_polytime (const _) (SoS.PolyTime.mulRaw' hd hp hp))

theorem hConstraint_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {p : α → RawPoly} {εh : α → ℚ}
    (hd : ComputableInPolyTime d enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly)
    (hh : ComputableInPolyTime εh enc encRat) :
    ComputableInPolyTime (fun a ↦ hConstraint (d a) (p a) (εh a))
      enc encRawPoly := by
  have hn := unary_add' hd hd
  unfold hConstraint radial
  exact listAppend' (NestedProgram.scale_polytime hh (listAppend'
    (SpecPoly.power_polytime_of 4 hn
      (pull_polytime_of hd (SpecPoly.normSq_polytime_of hd) (const 0) (const 1)))
    (SpecPoly.power_polytime_of 4 hn
      (pull_polytime_of hd (SpecPoly.normSq_polytime_of hd) (const 1) (const 0)))))
    (NestedProgram.scale_polytime (const _)
      (SoS.PolyTime.mulRaw' hn (hessian_polytime_of hd hp) (hessian_polytime_of hd hp)))

theorem plain_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {p : α → RawPoly} {εq : α → ℚ}
    (hd : ComputableInPolyTime d enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly)
    (hq : ComputableInPolyTime εq enc encRat) :
    ComputableInPolyTime (fun a ↦ plain (d a) (p a) (εq a))
      enc (encList encRawPoly) := by
  unfold plain
  exact cons' (listAppend' (const _)
    (NestedProgram.scale_polytime (const _) (SpecPoly.normSq_polytime_of hd)))
    (cons' (qConstraint_polytime_of hd hp hq) (const []))

noncomputable section

private theorem toReal_aeval {d n : ℕ} (f : Fin d → QPoly n) (p : QPoly d) :
    SoS.toReal (aeval f p) = aeval (fun i ↦ SoS.toReal (f i)) (SoS.toReal p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [SoS.toReal]
  | add p q hp hq => simp only [map_add, SoS.toReal_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, SoS.toReal_mul, hp]
    simp [SoS.toReal]

theorem images_getD (d : ℕ) (s t : ℚ) (i : Fin d) :
    (images d s t).getD i.val [] =
      [(NestedProgram.unitExp (d + d) i.val 1, s),
        (NestedProgram.unitExp (d + d) (d + i.val) 1, t)] :=
  FrameAux.Linear.getD_map_range _ _ i.isLt

theorem pull_toPoly (d : ℕ) (p : RawPoly) (s t : ℚ)
    (hp : ∀ z ∈ p, (SoS.Poly.expo d z.1).sum ≤ 4) :
    (pull d p s t).toPoly (d + d) =
      aeval (fun i : Fin d ↦ C s * X ⟨i.val, by omega⟩ +
        C t * X ⟨d + i.val, by omega⟩) (p.toPoly d) := by
  rw [pull, SpecPoly.substitute_agrees d (d + d) 4 16 2 p (images d s t)
    (by norm_num) (by norm_num) hp (fun i hi ↦ by
      rw [images_getD d s t ⟨i, hi⟩]
      exact ⟨by simp, by simp⟩)]
  apply congrArg (fun f : Fin d → QPoly (d + d) ↦ aeval f (p.toPoly d))
  funext i
  rw [images_getD, show ([(NestedProgram.unitExp (d + d) i.val 1, s),
      (NestedProgram.unitExp (d + d) (d + i.val) 1, t)] : RawPoly) =
      [(NestedProgram.unitExp (d + d) i.val 1, s)] ++
        [(NestedProgram.unitExp (d + d) (d + i.val) 1, t)] by rfl,
    SoS.Poly.toPoly_append, NestedProgram.unit_toPoly _ _ _ _ (by omega),
    NestedProgram.unit_toPoly _ _ _ _ (by omega)]
  simp only [pow_one]

theorem pull_real (d : ℕ) (p : RawPoly) (s t : ℚ)
    (hp : ∀ z ∈ p, (SoS.Poly.expo d z.1).sum ≤ 4) :
    rename (Rounding.sumIndex d) (SoS.toReal ((pull d p s t).toPoly (d + d))) =
      aeval (fun i : Fin d ↦ C (s : ℝ) * X (Sum.inl i) + C (t : ℝ) * X (Sum.inr i))
        (SoS.toReal (p.toPoly d)) := by
  rw [pull_toPoly d p s t hp, toReal_aeval, comp_aeval_apply]
  apply congrArg (fun f : Fin d → BiPoly d ↦ aeval f (SoS.toReal (p.toPoly d)))
  funext i
  simp [SoS.toReal, Rounding.sumIndex, i.isLt, show ¬d + i.val < d by omega]

private theorem normSq_degree (d : ℕ) :
    ∀ z ∈ MomentProgram.normSq d, (SoS.Poly.expo d z.1).sum ≤ 4 := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
  have hi' := List.mem_range.mp hi
  rw [← SoS.Mono.degree_toFinsupp (SoS.Poly.length_expo d _),
    SoS.Poly.toFinsupp_expo, MomentProgram.unitExp_toFinsupp _ _ _ hi',
    Finsupp.degree_single]
  norm_num

theorem radial_real (d : ℕ) (s t : ℚ) :
    rename (Rounding.sumIndex d) (SoS.toReal ((radial d s t).toPoly (d + d))) =
      ∑ i : Fin d, (C (s : ℝ) * X (Sum.inl i) + C (t : ℝ) * X (Sum.inr i)) ^ 2 := by
  rw [radial, pull_real d _ s t (normSq_degree d), MomentProgram.normSq_toPoly]
  simp [SoS.toReal]

private theorem real_scale (d : ℕ) (c : ℚ) (p : RawPoly) :
    rename (Rounding.sumIndex d)
      (SoS.toReal ((NestedProgram.scale c p).toPoly (d + d))) =
        C (c : ℝ) * rename (Rounding.sumIndex d) (SoS.toReal (p.toPoly (d + d))) := by
  simp [NestedProgram.scale_toPoly, SoS.toReal]

private theorem real_append (d : ℕ) (p q : RawPoly) :
    rename (Rounding.sumIndex d) (SoS.toReal ((p ++ q).toPoly (d + d))) =
      rename (Rounding.sumIndex d) (SoS.toReal (p.toPoly (d + d))) +
        rename (Rounding.sumIndex d) (SoS.toReal (q.toPoly (d + d))) := by
  simp [SoS.Poly.toPoly_append, SoS.toReal]

theorem hessian_real (d : ℕ) (p : RawPoly)
    (hp : ∀ z ∈ p, (SoS.Poly.expo d z.1).sum ≤ 4) :
    rename (Rounding.sumIndex d) (SoS.toReal ((hessian d p).toPoly (d + d))) =
      4 * Centered.polarize (SoS.toReal (p.toPoly d)) := by
  simp only [hessian, real_scale, real_append]
  rw [pull_real d p 1 1 hp, pull_real d p (-1) 1 hp,
    pull_real d p 0 1 hp, pull_real d p 1 0 hp]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_neg,
    Rat.cast_zero, map_one, map_zero, map_neg, one_mul, zero_mul, zero_add, add_zero,
    neg_one_mul]
  have hv : (aeval fun i : Fin d ↦ X (Sum.inr i)) (SoS.toReal (p.toPoly d)) =
      liftV (SoS.toReal (p.toPoly d)) := by
    rw [liftV, rename_eq_aeval]
    rfl
  have hu : (aeval fun i : Fin d ↦ X (Sum.inl i)) (SoS.toReal (p.toPoly d)) =
      liftU (SoS.toReal (p.toPoly d)) := by
    rw [liftU, rename_eq_aeval]
    rfl
  rw [hv, hu]
  have hplus : (fun i : Fin d ↦ X (Sum.inl i) + X (Sum.inr i) : Fin d → BiPoly d) =
      (fun i ↦ X (Sum.inr i) + X (Sum.inl i)) := by
    funext i
    exact add_comm _ _
  have hminus : (fun i : Fin d ↦ -X (Sum.inl i) + X (Sum.inr i) : Fin d → BiPoly d) =
      (fun i ↦ X (Sum.inr i) - X (Sum.inl i)) := by
    funext i
    abel
  rw [hplus, hminus]
  unfold Centered.polarize
  rw [show (1 / 3 : ℝ) = 4 * (1 / 12) by norm_num, map_mul]
  simp only [map_ofNat]
  ring

theorem qConstraint_real (d : ℕ) (p : RawPoly) (εq : ℚ) :
    SoS.toReal ((qConstraint d p εq).toPoly d) =
      Centered.qConstraint (SoS.toReal (p.toPoly d)) (εq : ℝ) := by
  simp only [qConstraint, SoS.Poly.toPoly_append, NestedProgram.scale_toPoly,
    MomentProgram.power_toPoly, SoS.Coords.toPoly_mulRaw, SoS.toReal_add,
    SoS.toReal_mul, SoS.toReal_pow, MomentProgram.normSq_toPoly]
  simp only [SoS.toReal, map_sum, map_pow, map_X, map_C, Centered.qConstraint, nsq]
  norm_num
  rw [show (1 / 9 : ℝ) = (1 / 3) ^ 2 by norm_num, map_pow]
  ring

private theorem real_mul (d : ℕ) (p q : RawPoly) :
    rename (Rounding.sumIndex d)
      (SoS.toReal ((SoS.Coords.mulRaw (d + d) p q).toPoly (d + d))) =
        rename (Rounding.sumIndex d) (SoS.toReal (p.toPoly (d + d))) *
          rename (Rounding.sumIndex d) (SoS.toReal (q.toPoly (d + d))) := by
  simp [SoS.Coords.toPoly_mulRaw, SoS.toReal]

private theorem real_power (d : ℕ) (p : RawPoly) (r : ℕ) :
    rename (Rounding.sumIndex d)
      (SoS.toReal ((MomentProgram.power (d + d) p r).toPoly (d + d))) =
        rename (Rounding.sumIndex d) (SoS.toReal (p.toPoly (d + d))) ^ r := by
  simp [MomentProgram.power_toPoly, SoS.toReal]

theorem hConstraint_real (d : ℕ) (p : RawPoly) (εh : ℚ)
    (hp : ∀ z ∈ p, (SoS.Poly.expo d z.1).sum ≤ 4) :
    rename (Rounding.sumIndex d) (SoS.toReal ((hConstraint d p εh).toPoly (d + d))) =
      Centered.hConstraint (SoS.toReal (p.toPoly d)) (εh : ℝ) := by
  simp only [hConstraint, real_append, real_scale, real_power, real_mul,
    hessian_real d p hp, radial_real]
  simp [Centered.hConstraint, liftV, liftU, nsq]
  ring

/-- Reification uses the same two plain constraints and the same single family slot. -/
theorem family_real (d : ℕ) (p : RawPoly) (εq εh : ℚ)
    (hp : ∀ z ∈ p, (SoS.Poly.expo d z.1).sum ≤ 4) :
    (family d p εq εh).real = Centered.system (SoS.toReal (p.toPoly d)) εq εh := by
  have hb : SoS.toReal ((NestedProgram.constant 1 ++
      NestedProgram.scale (-1) (MomentProgram.normSq d)).toPoly d) =
      1 - nsq := by
    simp [SoS.Poly.toPoly_append, NestedProgram.constant_toPoly,
      NestedProgram.scale_toPoly, MomentProgram.normSq_toPoly, SoS.toReal, nsq,
      sub_eq_add_neg]
  have hFs : ([hConstraint d p εh].map fun F ↦
      rename (Rounding.sumIndex d) (SoS.toReal (F.toPoly (d + d)))) =
      [Centered.hConstraint (SoS.toReal (p.toPoly d)) (εh : ℝ)] := by
    change [rename (Rounding.sumIndex d)
      (SoS.toReal ((hConstraint d p εh).toPoly (d + d)))] = _
    rw [hConstraint_real d p εh hp]
  dsimp only [family, Rounding.RawFamily.real, plain]
  simp only [hFs, List.map_cons, List.map_nil, hb, qConstraint_real, Centered.system]
  let mk (Fs : List (BiPoly d)) : Rounding.FamilySystem d :=
    ⟨[1 - nsq, Centered.qConstraint (SoS.toReal (p.toPoly d)) εq], Fs,
      [0].filterMap fun a ↦ if h : a < Fs.length then some ⟨a, h⟩ else none⟩
  exact congrArg mk hFs

theorem family_valid (d : ℕ) (p : RawPoly) (εq εh : ℚ)
    (hp : ∀ z ∈ p, (SoS.Poly.expo d z.1).sum ≤ 4)
    (hh : (p.toPoly d).IsHomogeneous 4) :
    Rounding.FamilySystem.Valid (d := d) (family d p εq εh).real 8 := by
  rw [family_real d p εq εh hp]
  have hpR : (SoS.toReal (p.toPoly d)).IsHomogeneous 4 := hh.map (algebraMap ℚ ℝ)
  have hq : (Centered.qConstraint (SoS.toReal (p.toPoly d)) εq).IsHomogeneous 8 := by
    exact ((Centered.IdentAux.nsq_homogeneous.pow 4).C_mul _).sub
      (by simpa only [Nat.reduceMul] using (hpR.C_mul (1 / 3)).pow 2)
  refine ⟨List.mem_cons_self, ?_, ?_⟩
  · intro f hf
    change f ∈ [1 - nsq, Centered.qConstraint (SoS.toReal (p.toPoly d)) εq] at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact (totalDegree_sub _ _).trans
        (max_le (by simp) (Centered.IdentAux.nsq_degree.trans (by norm_num)))
    · rw [List.mem_singleton.mp hf]
      exact hq.totalDegree_le
  · intro f hf
    change f ∈ [Centered.hConstraint (SoS.toReal (p.toPoly d)) εh] at hf
    rw [List.mem_singleton.mp hf]
    exact (Centered.IdentAux.hConstraint_homogeneous _ _ hpR).totalDegree_le

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecFamily
