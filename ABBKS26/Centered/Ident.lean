module

public import ABBKS26.Centered.IdentAuxEigen

/-!
# Identifiability of approximate eigenvectors and eigenspaces

[ABBKS26, Lemmas 5.11 and 5.12]: in sum-of-squares, a solution of the centered system has
small energy on the covariance deviations, so its projection on each eigenspace of large
deviation is small.
-/

@[expose] public section

namespace ABBKS26.Centered

noncomputable section


open Matrix

open Common MvPolynomial
variable {k d : ℕ}

/-- A Hessian instance proves small covariance-deviation energy. -/
theorem eval_ident
    (F : FrameModel k d) (w γ rF εq εh ε₁ W : ℝ) (i : Fin k)
    (hF : DataValid F w γ rF) (hw : w ≤ 1 / 2)
    (hε₁ : 0 < ε₁ ∧ ε₁ ≤ 1) (hq : 0 < εq) (hh : 0 < εh ∧ εh ≤ 16 * w ^ 2)
    (he : ((2 * εh + 32 * (1.1 / w) ^ 6 * εq) / (32 * w ^ 2)) ^
      (1 / 4 : ℝ) ≤ ε₁)
    (hW : 64 * (d + 1 : ℝ) ^ 2 + 1 / w + 1 / εq + 1 / ε₁ ≤ W) :
    SoS.DerivesNq ((system (psi F) εq εh).instances (fun _ ↦ deviation F i))
      8 (W ^ 20) 1 (C ε₁ - quad (deviation F i * deviation F i)) := by
  classical
  let E := deviation F i
  let e := 1.1 / w
  let Q := qConstraint (psi F) εq
  let H := inst (hConstraint (psi F) εh) E
  let t := 1 / (128 * w ^ 2 * ε₁ ^ 3)
  let aq := e ^ 6 * (1 / w) ^ 2 * (1 / εq) * (1 / ε₁) ^ 3 / 8
  let af := (1 / w) ^ 2 * (1 / ε₁) ^ 3 / 64
  have hw0 := hF.1.1
  have hεpos := hε₁.1
  have ht : 4 * t * (32 * w ^ 2) * ε₁ ^ 3 = 1 := by
    dsimp only [t]
    field_simp
    ring
  have hta : t * (16 * e ^ 6 / εq) = aq := by
    dsimp only [t, aq]
    field_simp
    ring
  have htf : 2 * t = af := by
    dsimp only [t, af]
    field_simp
    ring
  have haq : 0 ≤ aq := by dsimp only [aq]; positivity
  have haf : 0 ≤ af := by dsimp only [af]; positivity
  obtain ⟨hgap, hq1, hh4, he1⟩ :=
    IdentAux.tolerance_bounds w εq εh ε₁ hw0 hw hq hh hε₁ he
  have hs : Eᵀ = E := IdentAux.deviation_symm F
    (fun j ↦ (hF.1.2.2.2 j).isHermitian) i
  have hX : IsSumSq (quad (E * E)) := by
    apply SoSKit.psd_quad
    simpa only [conjTranspose_eq_transpose_of_trivial, hs] using
      posSemidef_conjTranspose_mul_self E
  have hR := IdentAux.root_remainder (quad (E * E)) Q H
    (2 * εh + 32 * e ^ 6 * εq) (32 * w ^ 2) (16 * e ^ 6 / εq) ε₁ t
    hε₁.1 (by positivity) hgap ht hX
    (IdentAux.centered_raw_certificate F w γ rF εq εh i hF hq hh.2)
  rw [hta, htf] at hR
  obtain ⟨hnX, hdQ, hnQ, hdH, hnH⟩ := IdentAux.data_polynomial_bounds F w γ rF εq εh
    i hF ⟨hq.le, hq1⟩ ⟨hh.1.le, hh4⟩ he1
  have hinst : (system (psi F) εq εh).instances (fun _ ↦ E) =
      [1 - nsq, Q, H] := by
    simp [system, Rounding.FamilySystem.instances, List.ofFn_succ, Q, H]
  have hball : 1 - nsq ∈ (system (psi F) εq εh).instances (fun _ ↦ E) := by
    rw [hinst]; simp
  have hQ : Q ∈ (system (psi F) εq εh).instances (fun _ ↦ E) := by
    rw [hinst]; simp
  have hH : H ∈ (system (psi F) εq εh).instances (fun _ ↦ E) := by
    rw [hinst]; simp
  have hproof := IdentAux.derive_linear
    ((system (psi F) εq εh).instances (fun _ ↦ E)) (quad (E * E)) Q H ε₁ aq af
    hε₁ haq haf hball hQ hH (IdentAux.quad_degree _) hdQ hdH hR
  apply hproof.mono le_rfl
  calc
    _ ≤ 1 + (d + 1 : ℝ) ^ 4 * e ^ 2 + 2 * (d + 1 : ℝ) ^ 4 +
        aq * (3 * (d + 1 : ℝ) ^ 8 * e ^ 4) +
        af * (153 * (d + 1 : ℝ) ^ 12 * e ^ 8) := by
      gcongr
    _ = 1 + (d + 1 : ℝ) ^ 4 * (1.1 * (1 / w)) ^ 2 + 2 * (d + 1 : ℝ) ^ 4 +
        3 / 8 * (d + 1 : ℝ) ^ 8 * (1.1 * (1 / w)) ^ 10 * (1 / w) ^ 2 *
          (1 / εq) * (1 / ε₁) ^ 3 +
        153 / 64 * (d + 1 : ℝ) ^ 12 * (1.1 * (1 / w)) ^ 8 * (1 / w) ^ 2 *
          (1 / ε₁) ^ 3 := by
      dsimp only [aq, af, e]
      ring
    _ ≤ W ^ 20 := IdentAux.numeric_budget (d + 1) (1 / w) (1 / εq) (1 / ε₁) W
      (by linarith [Nat.cast_nonneg (α := ℝ) d]) (by positivity) (by positivity)
      (by positivity) hW

/-- A bad-eigenvalue projection is controlled by deviation energy. -/
theorem eigen_ident
    (F : FrameModel k d) (w γ rF εq εh ε₁ δ W : ℝ) (i : Fin k) (P : Mat d)
    (hF : DataValid F w γ rF) (hδ : 0 < δ) (hP : Projection P)
    (hspec : LE (δ ^ 2 • P) ((F.cov i - 1) * (F.cov i - 1)))
    (hW₂ : 2 ≤ W) (hδW : 1 / δ ≤ W)
    (hW : 64 * (d + 1 : ℝ) ^ 2 + 1 / w ≤ W)
    (hev : SoS.DerivesNq
      ((system (psi F) εq εh).instances (fun _ ↦ deviation F i)) 8 (W ^ 20) 1
      (C ε₁ - quad (deviation F i * deviation F i))) :
    (system (psi F) εq εh).Derives 8 (W ^ 24)
      (Real.sqrt d * (1.1 / w)) (C ((2 * ε₁ + 2 * γ ^ 2) / δ ^ 2) - quad P) := by
  classical
  let E := deviation F i
  let S := averageCov F - 1
  let A := system (psi F) εq εh
  let c := 2 / δ ^ 2
  let b := 2 * γ ^ 2 / δ ^ 2
  let R := C c * quad (E * E) + C b * nsq - quad P
  have hw := hF.1.1
  have hW0 : 0 ≤ W := by linarith
  have hγ : 0 ≤ γ := hF.2.2.1.1
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  obtain ⟨hW4, hdW, heW, hcW, hbW⟩ := IdentAux.eigen_parameters w γ δ W hw hγ
    hF.2.2.2.1 hδ hW₂ hδW hW
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hsE := IdentAux.deviation_symm F (fun j ↦ (hF.1.2.2.2 j).isHermitian) i
  have hsS : Sᵀ = S := by
    simp only [S, transpose_sub, transpose_one,
      IdentAux.average_symm F (fun j ↦ (hF.1.2.2.2 j).isHermitian)]
  have hE := (deviation_bound F w γ rF hF).2 i
  have hS := IdentAux.average_error_bound F w γ rF hF
  have hR : IsSumSq R := by
    apply IdentAux.eigen_remainder E S P γ δ hδ hsE hsS hP hγ hS
    simpa only [E, S, deviation, sub_add_sub_cancel] using hspec
  obtain ⟨hnR, hdR⟩ := IdentAux.eigen_polynomial_bounds E P (1.1 / w) c b W
    hsE hP (by positivity) hE hW0 hdW heW hc0 hb0 hcW hbW
  have hevAt := IdentAux.system_derivesAt F εq εh (W ^ 20) E _ hev
  have hball : A.DerivesAt (fun _ ↦ E) 8 1 (1 - nsq) := by
    apply Rounding.FamilySystem.DerivesAt.of_plain
    · simp [A, system]
    · exact (totalDegree_sub _ _).trans (max_le (by simp)
        (IdentAux.nsq_degree.trans (by omega)))
  have hrem := Rounding.FamilySystem.DerivesAt.ofIsSOS A (fun _ ↦ E) hR hdR hnR
  have ht := ((hevAt.smul hc0).add (hball.smul hb0)).add hrem
  simp only [mul_one] at ht
  have hpoly : C c * (C ε₁ - quad (E * E)) + C b * (1 - nsq) + R =
      C ((2 * ε₁ + 2 * γ ^ 2) / δ ^ 2) - quad P := by
    dsimp only [R, b, c]
    simp only [div_eq_mul_inv, C_add, C_mul, map_ofNat]
    ring
  have hbudget := IdentAux.eigen_budget c b W hW4 hcW hbW
  refine ⟨fun _ ↦ E, ?_, (ht.congr hpoly).mono hbudget⟩
  intro a
  calc
    frobSq E ≤ d * (1.1 / w) ^ 2 := IdentAux.frob_bound E hsE _ (by positivity) hE
    _ = (Real.sqrt d * (1.1 / w)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hd0]

end

end ABBKS26.Centered
