module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdMoments

/-! The executable SUB moment input and its prepared sample allowance. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdInput

open Common Matrix FrameAux.Linear FrameAux.Features
open _root_.ABBKS26.Tree Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

variable {n k d : ℕ}

def degree (a : Args) : ℕ := IdCov.tDegree (field a 0)

theorem degree_polytime : ComputableInPolyTime degree encArgs encUnary := by
  unfold degree IdCov.tDegree logInv
  exact unary_add' (binary_clog_two.comp
    (FrameAux.Linear.rat_natCeil' (rat_inv' (field_polytime 0)))) (const 3)

def orders (a : Args) : List ℕ :=
  (List.range (4 * degree a + 1)).filter fun j ↦ 1 ≤ j

theorem orders_polytime : ComputableInPolyTime orders encArgs encIndices := by
  have hr : ComputableInPolyTime (fun a : Args ↦ List.range (4 * degree a + 1))
      encArgs encIndices := by
    have hm : ComputableInPolyTime (fun a : Args ↦
        (List.range (4 * degree a + 1)).map fun j ↦ j) encArgs encIndices := by
      apply mapWithInput
        (range.comp (unary_add' (unary_mul' (const 4) degree_polytime) (const 1)))
      exact unary_to_binary.comp (snd encArgs encUnary)
    exact hm.of_enc_eq fun a ↦ by simp
  apply filterWithInput
  · exact hr
  · exact binary_le' (const 1) (snd _ _)

def weight (a : Args) : ℚ :=
  ABBKS26.RefineAux.momentWeight (field a 0) (degree a)

theorem weight_polytime : ComputableInPolyTime weight encArgs encRat := by
  unfold weight ABBKS26.RefineAux.momentWeight
  exact rat_mul' (field_polytime 0) (rat_sub' (const 1) (rat_div' (const 1)
    (rat_mul' (const 100) (rat_natCast' (unary_to_binary.comp degree_polytime)))))

def points (a : Args) : Points :=
  transform a.1.1 (IdCenter.run a).2.1
    (translate a.1.1 a.1.2.2.2.1 (IdCenter.run a).2.2.1)

theorem points_polytime : ComputableInPolyTime points encArgs encPoints := by
  have hT := (fst _ _).comp ((snd _ _).comp IdCenter.run_polytime)
  have ha := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp IdCenter.run_polytime))
  exact transform_polytime (by fun_prop) hT (translate_polytime (by fun_prop)
    (by fun_prop) ha)

def input (a : Args) : MomentInput :=
  ((points a, a.1.2.2.2.2.2, orders a, weight a, field a 14), a.2)

theorem input_polytime : ComputableInPolyTime input encArgs encMomentInput :=
  (points_polytime.prod ((show ComputableInPolyTime
    (fun a : Args ↦ a.1.2.2.2.2.2) encArgs encIndices by fun_prop).prod
      (orders_polytime.prod (weight_polytime.prod (field_polytime 14))))).prod (snd _ _)

def run (MC : MomentCode) (a : Args) : List SoS.Solver.RawPoly := momentL MC (input a)

theorem run_polytime (MC : MomentCode) (hMC : MomentSpec MC) :
    ComputableInPolyTime (run MC) encArgs (encList SoS.Solver.encRawPoly) :=
  (moment_polytime MC hMC).comp input_polytime

theorem orders_agrees (a : Args) :
    orders a = (Finset.Icc 1 (4 * degree a)).sort (· ≤ ·) := by
  have he : (orders a).toFinset = Finset.Icc 1 (4 * degree a) := by
    ext j
    simp only [List.mem_toFinset, orders, List.mem_filter, List.mem_range,
      decide_eq_true_eq, Finset.mem_Icc]
    omega
  rw [← he]
  exact ((List.toFinset_sort (· ≤ ·) (List.nodup_range.filter _)).mpr
    (List.pairwise_le_range.filter _)).symm

theorem fuel_bound (k n d t : ℕ) (ps : ℕ → StepParams)
    (ht : t = IdCov.tDegree (ps 0).w) (J : Finset ℕ) (hJ : J.sup id ≤ 4 * t) :
    momentFuel n d J ≤ localBudget .identical k n d ps := by
  have ht0 : 1 ≤ t := by rw [ht]; unfold IdCov.tDegree; omega
  have htop : J.sup id + 1 ≤ 5 * t := by omega
  have hsquare : (J.sup id + 1) ^ 2 ≤ 25 * t ^ 2 := by
    have hb := Nat.pow_le_pow_left htop 2
    nlinarith only [hb]
  have hexp : 100 * (Rounding.solverConstant + 1) * (J.sup id + 1) ^ 2 ≤
      1000000000 * (Rounding.solverConstant + 1) * t ^ 2 := by
    have hb := Nat.mul_le_mul_left (100 * (Rounding.solverConstant + 1)) hsquare
    nlinarith only [hb]
  have hn : 1 ≤ n + d + 2 := by omega
  have hd : 1 ≤ d + 2 := by omega
  unfold momentFuel localBudget
  rw [ite_eq_right (by decide : Mode.identical ≠ .centered)]
  rw [show logInv (ps 0).w + 3 = t from ht.symm]
  calc
    _ ≤ (n + d + 2) ^ (1000000000 * (Rounding.solverConstant + 1)) *
        (d + 2) ^ (1000000000 * (Rounding.solverConstant + 1) * t ^ 2) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right hn (by omega))
        (Nat.pow_le_pow_right hd hexp)
    _ ≤ (branchCap .identical k ps + 1) ^ (k + 1) *
        ((n + d + 2) ^ (1000000000 * (Rounding.solverConstant + 1)) *
          (d + 2) ^ (1000000000 * (Rounding.solverConstant + 1) * t ^ 2)) :=
      Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
    _ ≤ _ := by
      simp only [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
        (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))))

noncomputable section

theorem affine_agrees (T : MatrixL) (a : Vector) (x : Fin n → Fin d → ℚ) :
    transform d T (translate d (pointsOf x) a) =
      pointsOf (ABBKS26.RefineAux.affinePoints x (matrixOf d T) (vectorOf d a)) := by
  apply List.ext_getElem
  · simp [transform, translate, table, pointsOf]
  · intro l hl hl'
    have hln : l < n := by simpa [pointsOf] using hl'
    simp only [transform, translate, table, pointsOf, List.length_ofFn,
      List.getElem_map, List.getElem_range, List.getElem_ofFn]
    apply List.ext_getElem
    · simp [mulVecL]
    · intro i hi hi'
      have hid : i < d := by simpa using hi'
      simp only [mulVecL, List.getElem_map, List.getElem_range, List.getElem_ofFn,
        ABBKS26.RefineAux.affinePoints]
      apply dotL_eq (fun _ ↦ rfl)
      intro j
      rw [getD_map_range _ _ j.isLt]
      simp [ent, List.getD_eq_getElem?_getD, hln, j.isLt, vectorOf]

theorem points_agrees (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    points (args k ps x h P, fuel) =
      pointsOf (ABBKS26.RefineAux.affinePoints x
        (IdFrame.frame (ps h) x fuel P).transform
        (IdFrame.frame (ps h) x fuel P).center) := by
  rw [IdFrame.frame_agrees ps x fuel h P hh]
  exact affine_agrees _ _ x

theorem input_agrees (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    input (args k ps x h P, fuel) =
      ((pointsOf (ABBKS26.RefineAux.affinePoints x
        (IdFrame.frame (ps h) x fuel P).transform
        (IdFrame.frame (ps h) x fuel P).center), indexList P,
        (Finset.Icc 1 (4 * IdCov.tDegree (ps h).w)).sort (· ≤ ·),
        ABBKS26.RefineAux.momentWeight (ps h).w (IdCov.tDegree (ps h).w),
        (ps h).contamination), fuel) := by
  have hw : field (args k ps x h P, fuel) 0 = (ps h).w := by
    rw [field_args _ _ _ _ _ _ hh]
    rfl
  have hc : field (args k ps x h P, fuel) 14 = (ps h).contamination := by
    rw [field_args _ _ _ _ _ _ hh]
    rfl
  simp only [input, points_agrees ps x fuel h P hh, orders_agrees, degree, weight, hw, hc]
  rfl

theorem run_agrees (MC : MomentCode) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k)
    (q : ℕ) :
    ((run MC (args k ps x h P, fuel)).getD q []).toPoly d =
      momentProc MC (ABBKS26.RefineAux.affinePoints x
        (IdFrame.frame (ps h) x fuel P).transform
        (IdFrame.frame (ps h) x fuel P).center) P
        (Finset.Icc 1 (4 * IdCov.tDegree (ps h).w))
        (ABBKS26.RefineAux.momentWeight (ps h).w (IdCov.tDegree (ps h).w))
        (ps h).contamination fuel q := by
  rw [run, input_agrees ps x fuel h P hh]
  rfl


/-- Both degree parameters use the same public weight on prepared inputs. -/
theorem prepared_degree (ps : ℕ → StepParams) (M : Mixture k d)
    (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d) (r : Rounding k d)
    (hp : Prepared .identical M ε w η Δ D ω r ps) (h : ℕ) (hh : h < k - 1) :
    IdCov.tDegree (ps h).w = IdCov.tDegree (ps 0).w := by
  have hw : (ps h).w = (ps 0).w := by
    exact_mod_cast (hp.weight_at .identical M ε w η Δ D ω r ps h (by omega)).trans
      (hp.weight_at .identical M ε w η Δ D ω r ps 0 (by omega)).symm
  rw [hw]

/-- The executable moment list certifies the same affine data used by SUB. -/
theorem prepared_certificate (MC : MomentCode) (hMC : MomentSpec MC)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card) :
    let Y := IdFrame.frame (ps h) x fuel P
    ∃ S : IdCov.Data I.card d,
      S.frame = (ABBKS26.RefineAux.affineReference
        (ABBKS26.RefineAux.roundedReference M ω r P I hI)
        (Y.transform.map (algebraMap ℚ ℝ)) (fun i ↦ (Y.center i : ℝ))).model ∧
      S.Valid (((ps h).w / 2 : ℚ) : ℝ) (ps h).isotropy ∧
      IdCov.momentCertificate S
        (fun q ↦ SoS.toReal (((run MC (args k ps x h P, fuel)).getD q []).toPoly d))
        (IdCov.tDegree (ps h).w) (ps h).momentError := by
  subst x
  let x := fun l i ↦ r ((ω l).1, (ω l).2.2) i
  let p := ps h
  let t := IdCov.tDegree p.w
  let Y := IdFrame.frame p x fuel P
  let J := Finset.Icc 1 (4 * t)
  obtain ⟨hclose, hm⟩ := IdFrame.prepared ps x fuel h P M ε w η Δ D ω r I hI
    rfl hp hf hh hl hP
  obtain ⟨S, hframe, hS⟩ := IdModel.data M ε w η Δ D ω r ps hp h hh P I hI
    hl hP Y hclose Y.center hm
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  obtain ⟨hw, hw2, _, _, _, _, _, _, _, _, _, _, hσ, hreq, _⟩ := hs
  have hσ1 : (1 : ℚ) ≤ p.sigmaSq :=
    ABBKS26.RefineAux.sigmaSq_one_le p hw hw2 hσ
  have he : p.contamination ≤ 1 / 64000 := by
    apply (hreq.trans (min_le_left _ _)).trans
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith only [hσ1]
  have heR : (p.contamination : ℝ) ≤ 1 / 64000 := by
    have hc := Rat.cast_le (K := ℝ) |>.mpr he
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hc
    exact hc
  have hsmall : sqnorm (Y.transform.map (algebraMap ℚ ℝ) *ᵥ
      ((fun i ↦ (Y.center i : ℝ)) -
        (ABBKS26.RefineAux.roundedReference M ω r P I hI).mean)) ≤ 1 / 100 := by
    exact hm.trans (by linarith only [heR])
  have htop : J.sup id ≤ 4 * t := Finset.sup_le fun q hq ↦ (Finset.mem_Icc.mp hq).2
  have hfuel : momentFuel n d J ≤ fuel :=
    (fuel_bound k n d t ps (prepared_degree ps M ε w η Δ D ω r hp h hh) J htop).trans hf
  have hc := IdMoments.certificate_of_center_bound M ε w η Δ D ω r ps hp h hh P I hI
    hl hP Y hclose MC hMC fuel Y.center hsmall hfuel J
    (fun q hq ↦ (Finset.mem_Icc.mp hq).1)
    (fun q hq ↦ (Finset.mem_Icc.mp hq).2)
  have hweight := hp.weight_at .identical M ε w η Δ D ω r ps h (by omega)
  have hS' : S.Valid (((ps h).w / 2 : ℚ) : ℝ) (ps h).isotropy := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, hweight] using hS
  have hc' := IdMoments.to_certificate S _ hframe _ t p.momentError hc
  have hagree : (fun q ↦ SoS.toReal
      (((run MC (args k ps x h P, fuel)).getD q []).toPoly d)) =
      (fun q ↦ SoS.toReal (momentProc MC
        (ABBKS26.RefineAux.affinePoints x Y.transform Y.center) P J
          (ABBKS26.RefineAux.momentWeight p.w t) p.contamination fuel q)) := by
    funext q
    exact congrArg SoS.toReal (run_agrees MC ps x fuel h P (by omega) q)
  exact ⟨S, hframe, hS', hagree.symm ▸ hc'⟩

/-- The executable estimates satisfy SUB's data and pre-rounding moment hypotheses. -/
theorem prepared_hypotheses (MC : MomentCode) (hMC : MomentSpec MC)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card) :
    let Y := IdFrame.frame (ps h) x fuel P
    let moments := fun q ↦ ((run MC (args k ps x h P, fuel)).getD q []).toPoly d
    ∃ S : IdCov.Data I.card d,
      S.frame = (ABBKS26.RefineAux.affineReference
        (ABBKS26.RefineAux.roundedReference M ω r P I hI)
        (Y.transform.map (algebraMap ℚ ℝ)) (fun i ↦ (Y.center i : ℝ))).model ∧
      S.Valid ((ps h).w / 2) (ps h).isotropy ∧
      ((ps h).isotropy : ℝ) ≤ IdCov.gammaStar (ps h).subspaceAccuracy ∧
      IdCov.momentCertificate S (fun q ↦ SoS.toReal (moments q))
        (IdCov.tDegree (ps h).w) (IdCov.etaStar (ps h).w (ps h).subspaceAccuracy / 4) := by
  obtain ⟨S, hframe, hS, hcert⟩ := prepared_certificate MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  obtain ⟨hw, hw2, hβ, hβ100, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := hs
  obtain ⟨_, _, _, hγ, he, _⟩ := hm
  rw [he] at hcert
  simp only [Rat.cast_div, Rat.cast_ofNat] at hcert
  have hS' : S.Valid ((ps h).w / 2) (ps h).isotropy := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hS
  exact ⟨S, hframe, hS', by exact_mod_cast hγ.le, hcert⟩

/-- The original projection-input adapter specializes the shared bounded SUB preparation. -/
theorem prepared_subspace (MC : MomentCode) (hMC : MomentSpec MC)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card) :
    let Y := IdFrame.frame (ps h) x fuel P
    let moments := fun q ↦ ((run MC (args k ps x h P, fuel)).getD q []).toPoly d
    ∃ S : IdCov.Data I.card d,
      S.frame = (ABBKS26.RefineAux.affineReference
        (ABBKS26.RefineAux.roundedReference M ω r P I hI)
        (Y.transform.map (algebraMap ℚ ℝ)) (fun i ↦ (Y.center i : ℝ))).model ∧
      ∃ Q : Mat d,
        (IdCov.SubspaceAux.input k d (ps h).w (ps h).subspaceAccuracy moments).Hypotheses
          [Q] ∧
        ∀ v, sqnorm v = 1 → qform S.cov v ≤ IdCov.tauStar (ps h).subspaceAccuracy →
          1 - (IdCov.epsilonR (ps h).subspaceAccuracy : ℝ) ≤ sqnorm (Q *ᵥ v) := by
  obtain ⟨S, hframe, hS, hγ, hcert⟩ := prepared_hypotheses MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  obtain ⟨hw, hw2, hβ, hβ100, _⟩ := hs
  obtain ⟨Q, hQ, hthin⟩ := IdCov.SubspaceAux.input_hypotheses_bounded S k
    (by simpa using Finset.card_le_univ I)
    (fun q ↦ ((run MC (args k ps x h P, fuel)).getD q []).toPoly d)
    (ps h).w (ps h).subspaceAccuracy (ps h).isotropy
    ⟨hw, hw2⟩ ⟨hβ, hβ100.trans (by norm_num)⟩ hS hγ hcert
  exact ⟨S, hframe, Q, hQ, hthin⟩

end

end ABBKS26.Assembly.Exec.RefineSynth.IdInput
