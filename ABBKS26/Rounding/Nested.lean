module

public import ABBKS26.Rounding.Family
public import ABBKS26.Rounding.NestedAux

/-!
# Nested sum-of-squares proofs as Gram variables

The system of [ABBKS26, Lemma 4.3] for the orthogonal complement: the inner sum-of-squares
proofs are encoded by bounded Gram variables, with its identity, feasibility and
concentration certificates.
-/

@[expose] public section

namespace ABBKS26.Rounding

noncomputable section


open Matrix

open Common MvPolynomial Matrix
open scoped BigOperators
variable {d : ℕ}

abbrev NPoly := MvPolynomial ℕ ℝ
abbrev Template (d : ℕ) := MvPolynomial (Fin d) NPoly

def monos (d e : ℕ) : List (Fin d →₀ ℕ) :=
  (SoS.Mono.all d e).map fun a ↦ Finsupp.equivFunOnFinite.symm (fun i ↦ a.getD i 0)

def constraintsWithOne (A : FamilySystem d) : List (RPoly d) := 1 :: A.plain

def gramSize (A : FamilySystem d) (deg j : ℕ) : ℕ :=
  (monos d ((deg - ((constraintsWithOne A)[j]?.getD 0).totalDegree) / 2)).length

def plainOffset (A : FamilySystem d) (deg j : ℕ) : ℕ :=
  d + ((List.range j).map fun i ↦ gramSize A deg i ^ 2).sum

def familySize (A : FamilySystem d) (deg a : ℕ) : ℕ :=
  let F := (A.families[a]?.getD 0)
  (monos d ((deg - F.totalDegree) / 2)).length

def slotOffset (A : FamilySystem d) (deg a : ℕ) : ℕ :=
  plainOffset A deg (A.plain.length + 1) +
    ((List.range a).map fun i ↦ familySize A deg (A.slots[i]?.map Fin.val |>.getD 0) ^ 2 +
      d ^ 2).sum

def nestedVars (A : FamilySystem d) (deg : ℕ) : ℕ :=
  slotOffset A deg A.slots.length

def gram (start : ℕ) (L : List (Fin d →₀ ℕ)) : Template d :=
  ∑ c : Fin L.length,
    (∑ a : Fin L.length, C (X (start + a * L.length + c)) * monomial L[a] 1) ^ 2

def embedCoeff (f : RPoly d) : Template d := f.map (MvPolynomial.C : ℝ →+* NPoly)

def xiLin (A : FamilySystem d) (deg a i : ℕ) : Template d :=
  ∑ j : Fin d, C (X (slotOffset A deg a +
    familySize A deg (A.slots[a]?.map Fin.val |>.getD 0) ^ 2 + i * d + j)) * X j

def template (A : FamilySystem d) (deg : ℕ) : Template d :=
  (∑ j : Fin (A.plain.length + 1),
    gram (plainOffset A deg j)
      (monos d ((deg - (constraintsWithOne A)[j].totalDegree) / 2)) *
        embedCoeff (constraintsWithOne A)[j]) +
  ∑ a : Fin A.slots.length,
    gram (slotOffset A deg a)
      (monos d ((deg - A.families[A.slots[a]].totalDegree) / 2)) *
      aeval (Sum.elim (fun i : Fin d ↦ xiLin A deg a i.val) X)
        (A.families[A.slots[a]].map (MvPolynomial.C : ℝ →+* NPoly))

def target (ε : ℝ) : Template d :=
  C (C (4 * ε) : NPoly) - (∑ i : Fin d, C (X i.val : NPoly) * X i) ^ 2

def coefficient (A : FamilySystem d) (deg : ℕ) (ε : ℝ) (μ : Fin d →₀ ℕ) : NPoly :=
  (target ε - template A deg).coeff μ

def nestedSystem (A : FamilySystem d) (deg : ℕ) (ε Bd : ℝ) : List NPoly :=
  let N : NPoly := ∑ i : Fin d, (X i.val : NPoly) ^ 2
  [N - 1, 1 - N] ++
    (monos d deg).flatMap (fun μ ↦ [coefficient A deg ε μ, -coefficient A deg ε μ]) ++
    [C Bd - ∑ i ∈ Finset.range (nestedVars A deg), X i ^ 2]

def outerDegree (A : FamilySystem d) : ℕ :=
  2 + (A.families.map MvPolynomial.totalDegree).foldl max 0

def solverDegree (A : FamilySystem d) (deg : ℕ) : ℕ :=
  2 * ((2 * deg + outerDegree A + 1) / 2)

/-- The constraint sum, coefficient equalities, and the K8 square-root step. -/
def nestedNorm (A : FamilySystem d) (deg : ℕ) (ε M : ℝ) : ℝ :=
  let b := (d + 1 : ℝ) ^ deg
  ((A.plain.length + 1 + A.slots.length) *
      (2 * (M + 1) * (d + 1 : ℝ) ^ (2 * deg) * b ^ 5) +
    b * (b + 1) ^ 2 + ((d + 1 : ℝ) ^ 2 + 2) ^ 2) / (4 * Real.sqrt ε) + 1

def gridConst (d e : ℕ) : ℝ := (d + 1 : ℝ) ^ e * (SoS.interpBound e : ℝ) ^ (2 * d) * (e + 1 : ℝ) ^ d

def ballBound (A : FamilySystem d) (deg : ℕ) (ε M Xb : ℝ) : ℝ :=
  2 + A.slots.length * Xb ^ 2 + (A.plain.length + 1 + A.slots.length) *
    gridConst d (deg / 2) * (deg / 2 + 1 : ℝ) ^ d *
      (2 * M + 2 * ε + 6 * (d + 1 : ℝ) ^ 2) * (deg / 2 : ℝ) ^ deg

def SatisfiesNested (A : FamilySystem d) (deg : ℕ) (ε Bd : ℝ)
    (y : ℕ → ℝ) : Prop := ∀ f ∈ nestedSystem A deg ε Bd, 0 ≤ eval y f

private theorem monos_length_le (d e : ℕ) : (monos d e).length ≤ (d + 1) ^ e := by
  simpa only [monos, List.length_map] using SoS.Mono.length_all_le d e

private theorem gramSize_sq_le (A : FamilySystem d) (deg j : ℕ) :
    gramSize A deg j ^ 2 ≤ (d + 1) ^ deg := by
  unfold gramSize
  calc
    _ ≤ ((d + 1) ^ ((deg - ((constraintsWithOne A)[j]?.getD 0).totalDegree) / 2)) ^ 2 :=
      Nat.pow_le_pow_left (monos_length_le _ _) _
    _ = (d + 1) ^ (((deg - ((constraintsWithOne A)[j]?.getD 0).totalDegree) / 2) * 2) :=
      (pow_mul _ _ _).symm
    _ ≤ (d + 1) ^ deg := Nat.pow_le_pow_right (by omega) (by omega)

private theorem familySize_sq_le (A : FamilySystem d) (deg a : ℕ) :
    familySize A deg a ^ 2 ≤ (d + 1) ^ deg := by
  unfold familySize
  calc
    _ ≤ ((d + 1) ^ ((deg - (A.families[a]?.getD 0).totalDegree) / 2)) ^ 2 :=
      Nat.pow_le_pow_left (monos_length_le _ _) _
    _ = (d + 1) ^ (((deg - (A.families[a]?.getD 0).totalDegree) / 2) * 2) :=
      (pow_mul _ _ _).symm
    _ ≤ (d + 1) ^ deg := Nat.pow_le_pow_right (by omega) (by omega)

private theorem range_sum_le (f : ℕ → ℕ) (n b : ℕ) (h : ∀ i < n, f i ≤ b) :
    ((List.range n).map f).sum ≤ n * b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simpa [Nat.add_mul] using Nat.add_le_add (ih fun i hi ↦ h i (by omega))
      (h n (by omega))

private theorem monos_nodup (d e : ℕ) : (monos d e).Nodup := by
  exact (SoS.Mono.nodup_all d e).map_on fun a ha b hb h ↦
    SoS.Mono.toFinsupp_inj (SoS.Mono.mem_all.1 ha).1 (SoS.Mono.mem_all.1 hb).1 h

private theorem mem_monos {e : ℕ} {μ : Fin d →₀ ℕ} :
    μ ∈ monos d e ↔ μ.degree ≤ e := by
  constructor
  · rintro h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
    exact (SoS.Mono.degree_toFinsupp (SoS.Mono.mem_all.1 ha).1).trans_le
      (SoS.Mono.mem_all.1 ha).2
  · intro h
    let a := List.ofFn fun i : Fin d ↦ μ i
    have ha : a.length = d := by simp [a]
    have he : SoS.Mono.toFinsupp d a = μ := by
      ext i
      simp [SoS.Mono.toFinsupp_apply, a]
    have hs : a.sum ≤ e := by
      rw [← SoS.Mono.degree_toFinsupp ha, he]
      exact h
    exact List.mem_map.2 ⟨a, SoS.Mono.mem_all.2 ⟨ha, hs⟩, he⟩

private theorem totalDegree_map_le {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : MvPolynomial σ R) : (p.map f).totalDegree ≤ p.totalDegree := by
  exact Finset.sup_mono (support_map_subset f p)

private theorem gram_degree (start e : ℕ) :
    (gram (d := d) start (monos d e)).totalDegree ≤ 2 * e := by
  apply totalDegree_finsetSum_le
  intro c _
  refine (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 ?_)
  apply totalDegree_finsetSum_le
  intro a _
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_monomial_le _ _).trans
    (mem_monos.1 (List.getElem_mem a.isLt))

private theorem xiLin_degree (A : FamilySystem d) (deg a i : ℕ) :
    (xiLin A deg a i).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by simp)

private theorem template_degree (A : FamilySystem d) (deg : ℕ) (hA : A.Valid deg) :
    (template A deg).totalDegree ≤ deg := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply totalDegree_finsetSum_le
    intro j _
    have hf : (constraintsWithOne A)[j].totalDegree ≤ deg := by
      have hm : (constraintsWithOne A)[j] ∈ 1 :: A.plain :=
        List.getElem_mem j.isLt
      rcases List.mem_cons.1 hm with h | h
      · rw [h]
        simp
      · exact hA.2.1 _ h
    refine (totalDegree_mul _ _).trans ?_
    have hg := gram_degree (d := d) (plainOffset A deg j)
      ((deg - (constraintsWithOne A)[j].totalDegree) / 2)
    have he := totalDegree_map_le (MvPolynomial.C : ℝ →+* NPoly) (constraintsWithOne A)[j]
    dsimp only [embedCoeff]
    omega
  · apply totalDegree_finsetSum_le
    intro a _
    have hf := hA.2.2 _ (List.getElem_mem (l := A.families) (A.slots[a]).isLt)
    have hg := gram_degree (d := d) (slotOffset A deg a)
      ((deg - A.families[A.slots[a]].totalDegree) / 2)
    have he := totalDegree_map_le (MvPolynomial.C : ℝ →+* NPoly) A.families[A.slots[a]]
    have hi := SoS.totalDegree_aeval_le
      (Sum.elim (fun i : Fin d ↦ xiLin A deg a i.val) X)
      (e := 1) (fun i ↦ by
        cases i with
        | inl i => exact xiLin_degree A deg a i
        | inr i => simp) (A.families[A.slots[a]].map (MvPolynomial.C : ℝ →+* NPoly))
    refine (totalDegree_mul _ _).trans ?_
    simp only [Fin.getElem_fin] at hf hg he hi ⊢
    omega

private theorem valid_degree (A : FamilySystem d) (deg : ℕ) (hA : A.Valid deg)
    (i : Fin d) : 2 ≤ deg := by
  have hcoeff : (1 - nsq : RPoly d).coeff (Finsupp.single i 2) = -1 := by
    have hz : (0 : Fin d →₀ ℕ) ≠ Finsupp.single i 2 := by
      intro h
      have := congrArg (fun f ↦ f i) h
      simp at this
    simp [nsq, coeff_X_pow, coeff_one, Finsupp.single_left_inj, hz]
  have hm : Finsupp.single i 2 ∈ (1 - nsq : RPoly d).support := by
    rw [mem_support_iff, hcoeff]
    norm_num
  have hd := (le_totalDegree hm).trans (hA.2.1 _ hA.1)
  simpa using hd

private theorem target_degree (A : FamilySystem d) (deg : ℕ) (ε : ℝ)
    (hA : A.Valid deg) : (target (d := d) ε).totalDegree ≤ deg := by
  unfold target
  apply (totalDegree_sub _ _).trans
  apply max_le (by rw [totalDegree_C]; exact Nat.zero_le _)
  by_cases hd : d = 0
  · subst d
    simp
  · have htwo := valid_degree A deg hA ⟨0, by omega⟩
    have hlin : (∑ i : Fin d, C (X i.val : NPoly) * X i).totalDegree ≤ 1 := by
      apply totalDegree_finsetSum_le
      intro i _
      exact (totalDegree_mul _ _).trans (by simp)
    exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul_left 2 hlin).trans htwo)

/-- Coefficient matching reconstructs the nested proof identity. -/
theorem nested_identity
    (A : FamilySystem d) (deg : ℕ) (ε : ℝ) (hA : A.Valid deg) :
    target ε - template A deg =
      ((monos d deg).map fun μ ↦ monomial μ (coefficient A deg ε μ)).sum := by
  classical
  let p := target (d := d) ε - template A deg
  have hd : p.totalDegree ≤ deg :=
    (totalDegree_sub _ _).trans
      (max_le (target_degree A deg ε hA) (template_degree A deg hA))
  rw [← List.sum_toFinset _ (monos_nodup d deg)]
  change p = ∑ μ ∈ (monos d deg).toFinset, monomial μ (p.coeff μ)
  conv_lhs => rw [p.as_sum]
  apply Finset.sum_subset
  · intro μ hμ
    exact List.mem_toFinset.2 (mem_monos.2 ((le_totalDegree hμ).trans hd))
  · intro μ _ hμ
    simp [notMem_support_iff.1 hμ]

/-- Both unit-sphere inequalities occur in the nested system. -/
theorem nested_sphere
    (A : FamilySystem d) (deg : ℕ) (ε Bd : ℝ) :
    SoS.DerivesNq (nestedSystem A deg ε Bd) 2 1 1
      ((∑ i : Fin d, (X i : NPoly) ^ 2) - 1) ∧
    SoS.DerivesNq (nestedSystem A deg ε Bd) 2 1 1
      (1 - ∑ i : Fin d, (X i : NPoly) ^ 2) := by
  have hn : (∑ i : Fin d, (X i.val : NPoly) ^ 2).totalDegree ≤ 2 :=
    totalDegree_finsetSum_le fun i _ ↦ by simp
  constructor
  · apply SoS.DerivesNq.of_mem
    · simp [nestedSystem]
    · exact (totalDegree_sub _ _).trans (max_le hn (by simp))
    · exact le_rfl
    · exact le_rfl
  · apply SoS.DerivesNq.of_mem
    · simp [nestedSystem]
    · exact (totalDegree_sub _ _).trans (max_le (by simp) hn)
    · exact le_rfl
    · exact le_rfl

private theorem sqnorm_nonneg (v : Vec d) : 0 ≤ sqnorm v := by
  change 0 ≤ ∑ i, v i * v i
  exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (v i)

private theorem dot_sq_le (v w : Vec d) : (v ⬝ᵥ w) ^ 2 ≤ sqnorm v * sqnorm w := by
  simpa only [dotProduct, sqnorm, pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w

private theorem sqnorm_entry_le (v : Vec d) (i : Fin d) : v i ^ 2 ≤ sqnorm v := by
  simpa only [sqnorm, dotProduct, pow_two] using
    Finset.single_le_sum (fun j _ ↦ mul_self_nonneg (v j)) (Finset.mem_univ i)

private theorem projection_dot (P : Mat d) (hp : Projection P) (v w : Vec d) :
    (P *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (P *ᵥ w) := by
  have h : v ᵥ* P = P *ᵥ v := by
    conv_lhs => rw [← hp.1]
    rw [vecMul_transpose]
  rw [dotProduct_mulVec, h]

private theorem projection_sqnorm (P : Mat d) (hp : Projection P) (v : Vec d) :
    sqnorm (P *ᵥ v) = v ⬝ᵥ (P *ᵥ v) := by
  rw [sqnorm, projection_dot P hp, mulVec_mulVec, hp.2]

private theorem projection_residual (P : Mat d) (hp : Projection P) (v : Vec d) :
    sqnorm (v - P *ᵥ v) = sqnorm v - sqnorm (P *ᵥ v) := by
  rw [sqnorm, sub_dotProduct, dotProduct_sub, dotProduct_sub,
    projection_dot P hp, ← projection_sqnorm P hp]
  dsimp only [sqnorm]
  ring

private theorem projection_contract (P : Mat d) (hp : Projection P) (v : Vec d) :
    sqnorm (P *ᵥ v) ≤ sqnorm v := by
  have h := sqnorm_nonneg (v - P *ᵥ v)
  rw [projection_residual P hp] at h
  linarith

private theorem projection_entry (P : Mat d) (hp : Projection P) (i j : Fin d) :
    |P i j| ≤ 1 := by
  have h := (sqnorm_entry_le (P *ᵥ Pi.single j 1) i).trans
    (projection_contract P hp (Pi.single j 1))
  have he : sqnorm (Pi.single j 1 : Vec d) = 1 := by
    rw [sqnorm, dotProduct_single, Pi.single_eq_same, mul_one]
  have hx : (P *ᵥ Pi.single j 1) i = P i j := by simp [mulVec_single]
  rw [he, hx] at h
  exact (sq_le_one_iff_abs_le_one _).1 h

private theorem quad_degree (P : Mat d) : (quad P).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  have hc : (C (P i j) * (X i : RPoly d)).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by simp)
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega)

private theorem quad_norm (Q : Mat d) (b : ℝ) (hb : ∀ i j, |Q i j| ≤ b) :
    SoS.coeffNorm1 (quad Q) ≤ d ^ 2 * b := by
  refine (SoS.coeffNorm1_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, b := by
      apply Finset.sum_le_sum
      intro i _
      refine (SoS.coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      calc
        _ ≤ SoS.coeffNorm1 (C (Q i j) * X i) * SoS.coeffNorm1 (X j) :=
          SoS.coeffNorm1_mul_le _ _
        _ = |Q i j| := by rw [SoS.coeffNorm1_C_mul, SoS.coeffNorm1_X,
            SoS.coeffNorm1_X, mul_one, mul_one]
        _ ≤ b := hb i j
    _ = _ := by simp; ring

private theorem quad_vecMulVec (w : Vec d) : quad (vecMulVec w w) = lin w ^ 2 := by
  simp only [quad, lin, pow_two, Finset.sum_mul_sum, vecMulVec_apply, C_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem quad_gap (P : Mat d) (w : Vec d) (δ : ℝ) :
    quad ((2 : ℝ) • P + (2 * δ) • (1 : Mat d) - vecMulVec w w) =
      C 2 * quad P + C (2 * δ) * nsq - lin w ^ 2 := by
  have hid : quad ((2 * δ) • (1 : Mat d)) = C (2 * δ) * nsq := by
    simp [quad, nsq, Matrix.one_apply, Finset.mul_sum, pow_two, mul_assoc,
      apply_ite, ite_mul]
  have hsm : quad ((2 : ℝ) • P) = C 2 * quad P := by
    simp [quad, Finset.mul_sum, mul_assoc, C_mul, smul_eq_mul]
  rw [← quad_vecMulVec, ← hsm, ← hid]
  simp [quad, C_add, C_sub, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

private theorem gap_psd (P : Mat d) (w : Vec d) (δ : ℝ)
    (hp : Projection P) (hw : sqnorm w = 1) (hδ : sqnorm (w - P *ᵥ w) ≤ δ) :
    ((2 : ℝ) • P + (2 * δ) • (1 : Mat d) - vecMulVec w w).PosSemidef := by
  have hsym : P.IsHermitian := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hp.1
  have hwmat : (vecMulVec w w).IsHermitian := by
    simp [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_vecMulVec]
  have htwo : IsSelfAdjoint (2 : ℝ) := by simp [IsSelfAdjoint]
  have hself : IsSelfAdjoint (2 * δ) := by simp [IsSelfAdjoint]
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    ((hsym.smul htwo).add (isHermitian_one.smul hself) |>.sub hwmat) fun v ↦ ?_
  have ha := dot_sq_le (P *ᵥ v) w
  rw [hw, mul_one, projection_dot P hp] at ha
  have hb := (dot_sq_le v (w - P *ᵥ w)).trans
    (mul_le_mul_of_nonneg_left hδ (sqnorm_nonneg v))
  have hab : v ⬝ᵥ w = v ⬝ᵥ (P *ᵥ w) + v ⬝ᵥ (w - P *ᵥ w) := by
    rw [dotProduct_sub]
    ring
  have hs := sq_nonneg (v ⬝ᵥ (P *ᵥ w) - v ⬝ᵥ (w - P *ᵥ w))
  have hbound : (v ⬝ᵥ w) ^ 2 ≤ 2 * sqnorm (P *ᵥ v) + 2 * δ * sqnorm v := by
    rw [hab]
    nlinarith
  rw [projection_sqnorm P hp] at hbound
  change 0 ≤ v ⬝ᵥ (((2 : ℝ) • P + (2 * δ) • (1 : Mat d) - vecMulVec w w) *ᵥ v)
  simp only [sub_mulVec, add_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec,
    dotProduct_sub, dotProduct_add, dotProduct_smul, op_smul_eq_smul, smul_eq_mul]
  rw [dotProduct_comm w v]
  simpa only [sqnorm, pow_two] using sub_nonneg.2 hbound

private theorem gap_norm (P : Mat d) (w : Vec d) (δ : ℝ)
    (hp : Projection P) (hw : sqnorm w = 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    SoS.coeffNorm1 (quad ((2 : ℝ) • P + (2 * δ) • (1 : Mat d) - vecMulVec w w)) ≤
      5 * (d : ℝ) ^ 2 := by
  have hw' : ∀ i, |w i| ≤ 1 := fun i ↦
    (sq_le_one_iff_abs_le_one _).1 (by simpa [hw] using sqnorm_entry_le w i)
  refine (quad_norm _ 5 fun i j ↦ ?_).trans_eq (by ring)
  have hid : |(1 : Mat d) i j| ≤ 1 := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    vecMulVec_apply]
  calc
    _ ≤ |2 * P i j| + |2 * δ * (1 : Mat d) i j| + |w i * w j| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = 2 * |P i j| + 2 * δ * |(1 : Mat d) i j| + |w i| * |w j| := by
      simp only [abs_mul, abs_of_nonneg hδ, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * 1 + 2 * 1 * 1 + 1 * 1 := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left (projection_entry P hp i j) (by norm_num))
          (mul_le_mul (mul_le_mul_of_nonneg_left hδ1 (by norm_num)) hid
            (abs_nonneg _) (by norm_num)))
        (mul_le_mul (hw' i) (hw' j) (abs_nonneg _) (by norm_num))
    _ = 5 := by norm_num

/-- A nearly projected target has a bounded nested certificate. -/
theorem target_derivation
    (A : FamilySystem d) (deg : ℕ) (ε M Xb : ℝ) (P : Mat d) (w : Vec d)
    (hA : A.Valid deg) (hp : Projection P) (hw : sqnorm w = 1) (hε : 0 < ε)
    (hnear : 1 - ε ≤ sqnorm (P *ᵥ w))
    (h : A.Derives deg M Xb (C ε - quad P)) :
    A.Derives deg (2 * M + 2 * ε + 6 * (d + 1 : ℝ) ^ 2) Xb
      (C (4 * ε) - lin w ^ 2) := by
  classical
  obtain ⟨Ξ, hΞ, h⟩ := h
  have hd : 0 < d := by
    by_contra! hd
    have hd' : d = 0 := by omega
    subst d
    simp [sqnorm, dotProduct] at hw
  have htwo := valid_degree A deg hA ⟨0, hd⟩
  let δ := min ε 1
  have hδ : 0 ≤ δ := le_min hε.le zero_le_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hres : sqnorm (w - P *ᵥ w) ≤ δ := by
    rw [projection_residual P hp, hw]
    exact le_min (by linarith) (by linarith [sqnorm_nonneg (P *ᵥ w)])
  let Q : Mat d := (2 : ℝ) • P + (2 * δ) • (1 : Mat d) - vecMulVec w w
  let s : RPoly d := quad Q + C (2 * (ε - δ))
  have hsos : IsSumSq s :=
    (SoSKit.psd_quad Q (gap_psd P w δ hp hw hres)).add
      (SoS.isSumSq_C (by linarith))
  have hsdeg : s.totalDegree ≤ deg :=
    (totalDegree_add _ _).trans
      (max_le ((quad_degree Q).trans htwo) (by rw [totalDegree_C]; omega))
  have hsnorm : SoS.coeffNorm1 s ≤ 5 * (d : ℝ) ^ 2 + 2 * (ε - δ) := by
    refine (SoS.coeffNorm1_add_le _ _).trans ?_
    rw [SoS.coeffNorm1_C, abs_of_nonneg (by linarith : 0 ≤ 2 * (ε - δ))]
    exact add_le_add (gap_norm P w δ hp hw hδ hδ1) le_rfl
  have hb : A.DerivesAt Ξ deg 1 (1 - nsq) :=
    FamilySystem.DerivesAt.of_plain hA.1 (hA.2.1 _ hA.1)
  have hs := FamilySystem.DerivesAt.ofIsSOS A Ξ hsos hsdeg hsnorm
  have ht := ((h.smul (c := 2) (by norm_num)).add
    (hb.smul (c := 2 * δ) (by positivity))).add hs
  refine ⟨Ξ, hΞ, ht.mono ?_ |>.congr ?_⟩
  · nlinarith [sq_nonneg (d : ℝ), Nat.cast_nonneg (α := ℝ) d]
  · dsimp only [s, Q]
    rw [quad_gap]
    simp only [map_sub, map_mul, map_ofNat]
    ring

private def plainIndex (A : FamilySystem d) (Ξ : Fin A.slots.length → Mat d)
    (j : Fin A.plain.length) : Fin (A.instances Ξ).length :=
  ⟨j, by simp [FamilySystem.instances]; omega⟩

private def plainMult (A : FamilySystem d) (Ξ : Fin A.slots.length → Mat d)
    {g : RPoly d} {deg : ℕ} (K : SoS.Proof (A.instances Ξ) g deg)
    (j : Fin (A.plain.length + 1)) : RPoly d :=
  Fin.cases (K.mult ∅) (fun i ↦ K.mult {plainIndex A Ξ i}) j

private theorem plainMult_sos (A : FamilySystem d) (Ξ : Fin A.slots.length → Mat d)
    {g : RPoly d} {deg : ℕ} (K : SoS.Proof (A.instances Ξ) g deg)
    (j : Fin (A.plain.length + 1)) : IsSumSq (plainMult A Ξ K j) := by
  induction j using Fin.cases with
  | zero => simpa [plainMult, SoS.IsSOS] using K.isSOS_mult ∅
  | succ j => simpa [plainMult, SoS.IsSOS] using K.isSOS_mult {plainIndex A Ξ j}

private theorem plainMult_degree (A : FamilySystem d) (Ξ : Fin A.slots.length → Mat d)
    {g : RPoly d} {deg : ℕ} (K : SoS.Proof (A.instances Ξ) g deg)
    (j : Fin (A.plain.length + 1)) :
    (plainMult A Ξ K j).totalDegree ≤ deg - (constraintsWithOne A)[j.val].totalDegree := by
  induction j using Fin.cases with
  | zero =>
    simp only [plainMult, Fin.cases_zero, constraintsWithOne, Fin.val_zero,
      List.getElem_cons_zero, totalDegree_one, Nat.sub_zero]
    by_cases hz : K.mult ∅ = 0
    · simp [hz]
    · simpa using K.degree_le ∅ hz
  | succ j =>
    simp only [plainMult, Fin.cases_succ, constraintsWithOne, Fin.val_succ,
      List.getElem_cons_succ]
    by_cases hz : K.mult {plainIndex A Ξ j} = 0
    · simp [hz]
    · have hd := K.degree_le {plainIndex A Ξ j} hz
      have he : (A.instances Ξ).get (plainIndex A Ξ j) = A.plain[j] := by
        simp [plainIndex, FamilySystem.instances, List.getElem_append_left j.isLt]
      simpa only [SoS.System.degree, Finset.sum_singleton, he, Fin.getElem_fin] using
        (Nat.le_sub_of_add_le hd)

private theorem plainMult_norm (A : FamilySystem d) (Ξ : Fin A.slots.length → Mat d)
    {g : RPoly d} {deg : ℕ} (K : SoS.Proof (A.instances Ξ) g deg) {M : ℝ}
    (hn : ∀ S, SoS.coeffNorm1 (K.mult S) ≤ M) (j : Fin (A.plain.length + 1)) :
    SoS.coeffNorm1 (plainMult A Ξ K j) ≤ M := by
  induction j using Fin.cases with
  | zero => exact hn ∅
  | succ j => exact hn {plainIndex A Ξ j}

private theorem certificate_expansion (A : FamilySystem d)
    (Ξ : Fin A.slots.length → Mat d) {g : RPoly d} {deg : ℕ}
    (K : SoS.Proof (A.instances Ξ) g deg) (hq : ∀ S, 1 < S.card → K.mult S = 0) :
    g = (∑ j : Fin (A.plain.length + 1),
      plainMult A Ξ K j * (constraintsWithOne A)[j.val]) +
      ∑ a : Fin A.slots.length,
        K.mult {A.slotIndex Ξ a} * inst A.families[(A.slots[a.val]).val] (Ξ a) := by
  classical
  rw [Fin.sum_univ_succ]
  simp only [plainMult, Fin.cases_zero, Fin.cases_succ, constraintsWithOne,
    Fin.val_zero, Fin.val_succ, List.getElem_cons_zero,
    List.getElem_cons_succ, mul_one]
  conv_lhs => rw [K.eq_sum_linear hq]
  rw [add_assoc]
  congr 1
  let e : Fin (A.plain.length + A.slots.length) ≃ Fin (A.instances Ξ).length :=
    finCongr (by simp [FamilySystem.instances])
  rw [← Equiv.sum_comp e]
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    have hi : e (Fin.castAdd A.slots.length j) = plainIndex A Ξ j := by rfl
    rw [hi]
    simp [plainIndex, FamilySystem.instances, List.getElem_append_left j.isLt]
  · apply Finset.sum_congr rfl
    intro a _
    have hi : e (Fin.natAdd A.plain.length a) = A.slotIndex Ξ a := by rfl
    rw [hi]
    simp [FamilySystem.slotIndex, FamilySystem.instances]

private theorem gram_bounded (deg : ℕ) (M : ℝ) (p : RPoly d) (e : ℕ)
    (hp : IsSumSq p) (hd : p.totalDegree ≤ 2 * e) (he : e ≤ deg / 2)
    (hn : SoS.coeffNorm1 p ≤ M) (htwo : 2 ≤ deg) :
    ∃ G : Matrix (Fin (monos d e).length) (Fin (monos d e).length) ℝ,
      p = ∑ c, (∑ a, C (G a c) * monomial (monos d e)[a] 1) ^ 2 ∧
      (∑ a, ∑ c, G a c ^ 2) ≤
        gridConst d (deg / 2) * (deg / 2 + 1 : ℝ) ^ d * M * (deg / 2 : ℝ) ^ deg := by
  classical
  -- Interpolate on the common grid, even when this multiplier has a smaller degree.
  obtain ⟨G, hg, hG⟩ := NestedAux.boundedGram (monos d e) (monos_nodup d e)
    (fun μ ↦ mem_monos) p hp hd
  -- A larger interpolation grid gives the same compression and a uniform estimate.
  have hgrid : gridConst d e ≤ gridConst d (deg / 2) := by
    have hi : SoS.interpBound e ≤ SoS.interpBound (deg / 2) := by
      unfold SoS.interpBound
      apply Nat.mul_le_mul (Nat.factorial_le (Nat.add_le_add_right he 1))
      have hbase : (e + 1) ^ e ≤ (deg / 2 + 1) ^ (deg / 2) :=
        (Nat.pow_le_pow_left (by omega) e).trans
          (Nat.pow_le_pow_right (by omega) he)
      exact (Nat.pow_le_pow_left hbase (e + 1)).trans
        (Nat.pow_le_pow_right (by positivity) (by omega))
    unfold gridConst
    gcongr; norm_num
  have hM : 0 ≤ M := (SoS.coeffNorm1_nonneg p).trans hn
  have hb : (1 : ℝ) ≤ deg / 2 := by
    have : (2 : ℝ) ≤ deg := by exact_mod_cast htwo
    linarith
  have he' : (e : ℝ) ≤ (deg : ℝ) / 2 := by
    have : 2 * e ≤ deg := by omega
    have : (2 : ℝ) * e ≤ deg := by exact_mod_cast this
    linarith
  have hgc : ∀ e, 0 ≤ gridConst d e := fun e ↦ by unfold gridConst; positivity
  have hval : ∀ x : Fin d → Fin (e + 1),
      eval (SoS.gridPoint x) p ≤ M * (deg / 2 : ℝ) ^ deg := by
    intro x
    refine (le_abs_self _).trans ((SoS.abs_eval_le hb ?_).trans ?_)
    · intro i
      simp only [SoS.gridPoint, Nat.abs_cast]
      exact (show ((x i).val : ℝ) ≤ e by exact_mod_cast Nat.lt_succ_iff.1 (x i).isLt).trans he'
    · exact mul_le_mul hn (pow_le_pow_right₀ hb (by omega))
        (pow_nonneg (by positivity) _) hM
  refine ⟨G, hg, hG.trans ?_⟩
  change gridConst d e * _ ≤ _
  calc
    _ ≤ gridConst d e * ((e + 1 : ℝ) ^ d * (M * (deg / 2 : ℝ) ^ deg)) := by
      apply mul_le_mul_of_nonneg_left _ (hgc e)
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun x _ ↦ hval x)
    _ ≤ gridConst d (deg / 2) * ((deg / 2 + 1 : ℝ) ^ d *
        (M * (deg / 2 : ℝ) ^ deg)) := by
      gcongr; exact hgc _
    _ = _ := by ring

private theorem pack_grams (A : FamilySystem d) (deg : ℕ) (w : Vec d)
    (Ξ : Fin A.slots.length → Mat d)
    (Gp : (j : Fin (A.plain.length + 1)) → Matrix
      (Fin (monos d ((deg - (constraintsWithOne A)[j.val].totalDegree) / 2)).length)
      (Fin (monos d ((deg - (constraintsWithOne A)[j.val].totalDegree) / 2)).length) ℝ)
    (Gs : (a : Fin A.slots.length) → Matrix
      (Fin (monos d ((deg - A.families[(A.slots[a.val]).val].totalDegree) / 2)).length)
      (Fin (monos d ((deg - A.families[(A.slots[a.val]).val].totalDegree) / 2)).length) ℝ)
    (T Xb Bd : ℝ) (hw : sqnorm w = 1)
    (hΞ : ∀ a, frobSq (Ξ a) ≤ Xb ^ 2)
    (hGpbound : ∀ j, (∑ a, ∑ c, Gp j a c ^ 2) ≤ T)
    (hGsbound : ∀ a, (∑ b, ∑ c, Gs a b c ^ 2) ≤ T)
    (hBd : 1 + (A.plain.length + 1 : ℕ) * T +
      A.slots.length * (T + Xb ^ 2) ≤ Bd) :
    ∃ y : ℕ → ℝ,
      (∀ i : Fin d, y i = w i) ∧
      (∀ (j : Fin (A.plain.length + 1))
      (a c : Fin (monos d ((deg - (constraintsWithOne A)[j.val].totalDegree) / 2)).length),
      y (plainOffset A deg j + a *
        (monos d ((deg - (constraintsWithOne A)[j.val].totalDegree) / 2)).length + c) =
          Gp j a c) ∧
      (∀ (a : Fin A.slots.length)
      (b c : Fin (monos d ((deg - A.families[(A.slots[a.val]).val].totalDegree) / 2)).length),
      y (slotOffset A deg a + b *
        (monos d ((deg - A.families[(A.slots[a.val]).val].totalDegree) / 2)).length + c) =
          Gs a b c) ∧
      (∀ (a : Fin A.slots.length) (i j : Fin d),
      y (slotOffset A deg a +
        familySize A deg (A.slots[a.val]?.map Fin.val |>.getD 0) ^ 2 + i * d + j) = Ξ a i j) ∧
      (∑ i ∈ Finset.range (nestedVars A deg), y i ^ 2) ≤ Bd := by
  classical
  let bp : ℕ → List ℝ := fun j ↦
    if hj : j < A.plain.length + 1 then NestedAux.matrixData (Gp ⟨j, hj⟩) else []
  let bs : ℕ → List ℝ := fun a ↦
    if ha : a < A.slots.length then
      NestedAux.matrixData (Gs ⟨a, ha⟩) ++ NestedAux.matrixData (Ξ ⟨a, ha⟩) else []
  have hbp (j : ℕ) (hj : j < A.plain.length + 1) :
      (bp j).length = gramSize A deg j ^ 2 := by
    simp only [bp, dite_eq_left hj, NestedAux.matrixData_length]
    simp only [gramSize, List.getElem?_eq_getElem
      (show j < (constraintsWithOne A).length by simpa [constraintsWithOne] using hj),
      Option.getD_some, pow_two]
  have hbs (a : ℕ) (ha : a < A.slots.length) :
      (bs a).length = familySize A deg (A.slots[a]?.map Fin.val |>.getD 0) ^ 2 + d ^ 2 := by
    simp [bs, ha, NestedAux.matrixData_length, familySize,
      pow_two]
  have hplen (j : ℕ) (hj : j ≤ A.plain.length + 1) :
      ((List.range j).map fun i ↦ (bp i).length).sum =
        ((List.range j).map fun i ↦ gramSize A deg i ^ 2).sum := by
    congr 1
    exact List.map_congr_left fun i hi ↦ hbp i (by have := List.mem_range.1 hi; omega)
  have hslen (a : ℕ) (ha : a ≤ A.slots.length) :
      ((List.range a).map fun i ↦ (bs i).length).sum =
        ((List.range a).map fun i ↦
          familySize A deg (A.slots[i]?.map Fin.val |>.getD 0) ^ 2 + d ^ 2).sum := by
    congr 1
    exact List.map_congr_left fun i hi ↦ hbs i (by have := List.mem_range.1 hi; omega)
  let pre := List.ofFn w
  let data := pre ++ (NestedAux.pack bp (A.plain.length + 1) ++
    NestedAux.pack bs A.slots.length)
  let y : ℕ → ℝ := fun i ↦ data.getD i 0
  have hlen : data.length = nestedVars A deg := by
    simp only [data, pre, List.length_append, List.length_ofFn, NestedAux.pack_length,
      hplen _ le_rfl, hslen _ le_rfl, nestedVars, slotOffset, plainOffset]
    omega
  have hy : ∀ i : Fin d, y i = w i := by
    intro i
    dsimp [y, data]
    rw [List.getD_append _ _ _ _ (by simp [pre])]
    simp [pre, i.isLt]
  have hyp : ∀ (j : Fin (A.plain.length + 1))
      (a c : Fin (monos d ((deg - (constraintsWithOne A)[j.val].totalDegree) / 2)).length),
      y (plainOffset A deg j + a *
        (monos d ((deg - (constraintsWithOne A)[j.val].totalDegree) / 2)).length + c) =
          Gp j a c := by
    intro j a c
    have hk : a * (monos d ((deg - (constraintsWithOne A)[j.val].totalDegree) / 2)).length + c <
        (bp j).length := by
      simp only [bp, dite_eq_left j.isLt, NestedAux.matrixData_length]
      have hh := (finProdFinEquiv (a, c)).isLt
      simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.add_comm, Nat.mul_comm] using hh
    have he := NestedAux.pack_get_inside bp pre (NestedAux.pack bs A.slots.length) j.isLt hk
    rw [hplen _ (by omega)] at he
    convert he.trans (show (bp j).getD _ 0 = Gp j a c by
      simp only [bp, dite_eq_left j.isLt]
      exact NestedAux.matrixData_get _ a c) using 1
    simp [y, data, pre, plainOffset, add_assoc]
  have hys : ∀ (a : Fin A.slots.length)
      (b c : Fin (monos d ((deg - A.families[(A.slots[a.val]).val].totalDegree) / 2)).length),
      y (slotOffset A deg a + b *
        (monos d ((deg - A.families[(A.slots[a.val]).val].totalDegree) / 2)).length + c) =
          Gs a b c := by
    intro a b c
    let n := (monos d ((deg - A.families[(A.slots[a.val]).val].totalDegree) / 2)).length
    have hk : b * n + c < n * n := by
      have := (finProdFinEquiv (b, c)).isLt
      simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.mul_comm, Nat.add_comm] using this
    have he := NestedAux.pack_get_inside bs
      (pre ++ NestedAux.pack bp (A.plain.length + 1)) [] a.isLt
      (show b * n + c < (bs a).length by
        dsimp only [bs]
        rw [dite_eq_left a.isLt]
        simp only [List.length_append, NestedAux.matrixData_length]
        change b * n + c < n * n + d * d
        omega)
    rw [hslen _ (by omega)] at he
    have he' : (bs a).getD (b * n + c) 0 = Gs a b c := by
      dsimp only [bs]
      rw [dite_eq_left a.isLt, List.getD_append _ _ _ _ (by simpa [n] using hk)]
      exact NestedAux.matrixData_get _ b c
    convert he.trans he' using 1
    simp [y, data, pre, List.append_assoc, NestedAux.pack_length, hplen _ le_rfl,
      slotOffset, plainOffset, n, add_assoc]
  have hyΞ : ∀ (a : Fin A.slots.length) (i j : Fin d),
      y (slotOffset A deg a +
        familySize A deg (A.slots[a.val]?.map Fin.val |>.getD 0) ^ 2 + i * d + j) = Ξ a i j := by
    intro a i j
    have hg : familySize A deg (A.slots[a.val]?.map Fin.val |>.getD 0) ^ 2 =
        (NestedAux.matrixData (Gs a)).length := by
      simp [familySize, pow_two]
    have hk : i * d + j < d * d := by
      have := (finProdFinEquiv (i, j)).isLt
      simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.mul_comm, Nat.add_comm] using this
    have he := NestedAux.pack_get_inside bs
      (pre ++ NestedAux.pack bp (A.plain.length + 1)) [] a.isLt
      (show (NestedAux.matrixData (Gs a)).length + (i * d + j) < (bs a).length by
        dsimp only [bs]
        rw [dite_eq_left a.isLt]
        rw [List.length_append, NestedAux.matrixData_length (Ξ _)]
        change (NestedAux.matrixData (Gs a)).length + (i * d + j) <
          (NestedAux.matrixData (Gs a)).length + d * d
        omega)
    rw [hslen _ (by omega)] at he
    have he' : (bs a).getD ((NestedAux.matrixData (Gs a)).length + (i * d + j)) 0 =
        Ξ a i j := by
      dsimp only [bs]
      rw [dite_eq_left a.isLt]
      change (NestedAux.matrixData (Gs a) ++ NestedAux.matrixData (Ξ a)).getD
        ((NestedAux.matrixData (Gs a)).length + (i * d + j)) 0 = _
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
      exact NestedAux.matrixData_get _ i j
    convert he.trans he' using 1
    simp [y, data, pre, List.append_assoc, NestedAux.pack_length, hplen _ le_rfl,
      slotOffset, plainOffset, familySize, pow_two, add_assoc]
  have hpre : (pre.map fun x ↦ x ^ 2).sum = 1 := by
    simpa [pre, List.map_ofFn, List.sum_ofFn, sqnorm, dotProduct, pow_two] using hw
  have hbpSq : ((NestedAux.pack bp (A.plain.length + 1)).map fun x ↦ x ^ 2).sum ≤
      (A.plain.length + 1 : ℕ) * T := by
    apply NestedAux.pack_sq_le
    intro j hj
    dsimp only [bp]
    rw [dite_eq_left hj, NestedAux.matrixData_sq]
    exact hGpbound ⟨j, hj⟩
  have hbsSq : ((NestedAux.pack bs A.slots.length).map fun x ↦ x ^ 2).sum ≤
      A.slots.length * (T + Xb ^ 2) := by
    apply NestedAux.pack_sq_le
    intro a ha
    dsimp only [bs]
    rw [dite_eq_left ha, List.map_append, List.sum_append,
      NestedAux.matrixData_sq, NestedAux.matrixData_sq]
    exact add_le_add (hGsbound ⟨a, ha⟩) (hΞ ⟨a, ha⟩)
  have hball : ∑ i ∈ Finset.range (nestedVars A deg), y i ^ 2 ≤ Bd := by
    change ∑ i ∈ Finset.range (nestedVars A deg), data.getD i 0 ^ 2 ≤ Bd
    rw [← hlen, NestedAux.sum_getD_sq]
    simp only [data, List.map_append, List.sum_append, hpre]
    linarith
  exact ⟨y, hy, hyp, hys, hyΞ, hball⟩

/-- Bounded Gram factors extend every target inside the explicit ball. -/
theorem nested_feasible
    (A : FamilySystem d) (deg : ℕ) (ε M Xb Bd : ℝ) (P : Mat d) (w : Vec d)
    (hA : A.Valid deg) (hp : Projection P) (hw : sqnorm w = 1) (hε : 0 < ε)
    (hnear : 1 - ε ≤ sqnorm (P *ᵥ w)) (hBd : ballBound A deg ε M Xb ≤ Bd)
    (h : A.Derives deg M Xb (C ε - quad P)) :
    ∃ y, (∀ i : Fin d, y i = w i) ∧ SatisfiesNested A deg ε Bd y := by
  classical
  have hd : 0 < d := by
    by_contra! hd
    have : d = 0 := by omega
    subst d
    simp [sqnorm, dotProduct] at hw
  have htwo := valid_degree A deg hA ⟨0, hd⟩
  let B := 2 * M + 2 * ε + 6 * (d + 1 : ℝ) ^ 2
  let T := gridConst d (deg / 2) * (deg / 2 + 1 : ℝ) ^ d * B * (deg / 2 : ℝ) ^ deg
  obtain ⟨Ξ, hΞ, K, hn, hq, hbudget⟩ :=
    target_derivation A deg ε M Xb P w hA hp hw hε hnear h
  have hGp : ∀ j : Fin (A.plain.length + 1),
      ∃ G : Matrix
        (Fin (monos d ((deg - (constraintsWithOne A)[j.val].totalDegree) / 2)).length)
        (Fin (monos d ((deg - (constraintsWithOne A)[j.val].totalDegree) / 2)).length) ℝ,
        plainMult A Ξ K j = ∑ c, (∑ a, C (G a c) *
          monomial (monos d ((deg - (constraintsWithOne A)[j.val].totalDegree) / 2))[a] 1) ^ 2 ∧
        (∑ a, ∑ c, G a c ^ 2) ≤ T := by
    intro j
    exact gram_bounded deg B _ _ (plainMult_sos A Ξ K j)
      (NestedAux.sos_budget (plainMult_sos A Ξ K j) (plainMult_degree A Ξ K j))
      (by omega) (plainMult_norm A Ξ K hn j) htwo
  choose Gp hGpeq hGpbound using hGp
  have hGs : ∀ a : Fin A.slots.length,
      ∃ G : Matrix
        (Fin (monos d ((deg - A.families[(A.slots[a.val]).val].totalDegree) / 2)).length)
        (Fin (monos d ((deg - A.families[(A.slots[a.val]).val].totalDegree) / 2)).length) ℝ,
        K.mult {A.slotIndex Ξ a} = ∑ c, (∑ b, C (G b c) *
          monomial (monos d ((deg - A.families[(A.slots[a.val]).val].totalDegree) / 2))[b] 1) ^ 2 ∧
        (∑ b, ∑ c, G b c ^ 2) ≤ T := by
    intro a
    have hs : IsSumSq (K.mult {A.slotIndex Ξ a}) := by
      simpa [SoS.IsSOS] using K.isSOS_mult {A.slotIndex Ξ a}
    have hdeg : (K.mult {A.slotIndex Ξ a}).totalDegree ≤
        deg - A.families[(A.slots[a.val]).val].totalDegree := by
      by_cases hz : K.mult {A.slotIndex Ξ a} = 0
      · simp [hz]
      · simpa only [Fin.getElem_fin] using Nat.le_sub_of_add_le (hbudget a hz)
    exact gram_bounded deg B _ _ hs (NestedAux.sos_budget hs hdeg)
      (by omega) (hn _) htwo
  choose Gs hGseq hGsbound using hGs
  have htotal : 1 + (A.plain.length + 1 : ℕ) * T +
      A.slots.length * (T + Xb ^ 2) ≤ Bd := by
    dsimp only [ballBound] at hBd
    dsimp only [T, B]
    push_cast at hBd ⊢
    nlinarith
  obtain ⟨y, hy, hyp, hys, hyΞ, hball⟩ :=
    pack_grams A deg w Ξ Gp Gs T Xb Bd hw hΞ hGpbound hGsbound htotal
  have hgplain (j : Fin (A.plain.length + 1)) :
      (gram (plainOffset A deg j)
        (monos d ((deg - (constraintsWithOne A)[j.val].totalDegree) / 2))).map (eval y) =
          plainMult A Ξ K j := by
    rw [hGpeq j]
    simp only [gram, map_sum, map_pow, map_mul, map_C, map_monomial, map_one, eval_X]
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [hyp j a c]
  have hgslot (a : Fin A.slots.length) :
      (gram (slotOffset A deg a)
        (monos d ((deg - A.families[(A.slots[a.val]).val].totalDegree) / 2))).map (eval y) =
          K.mult {A.slotIndex Ξ a} := by
    rw [hGseq a]
    simp only [gram, map_sum, map_pow, map_mul, map_C, map_monomial, map_one, eval_X]
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    rw [hys a b c]
  have hxi (a : Fin A.slots.length) (i : Fin d) :
      (xiLin A deg a i).map (eval y) = lin (Ξ a i) := by
    simp only [xiLin, lin, map_sum, map_mul, map_C, eval_X, map_X]
    apply Finset.sum_congr rfl
    intro j _
    rw [hyΞ a i j]
  have hinst (a : Fin A.slots.length) (F : BiPoly d) :
      (aeval (Sum.elim (fun i : Fin d ↦ xiLin A deg a i.val) X)
        (F.map (MvPolynomial.C : ℝ →+* NPoly))).map (eval y) = inst F (Ξ a) := by
    let ψ := Sum.elim (fun i : Fin d ↦ xiLin A deg a i.val) (X : Fin d → Template d)
    have he : ((map (eval y)).comp (aeval ψ).toRingHom).comp
        (map (MvPolynomial.C : ℝ →+* NPoly)) =
          (aeval (Sum.elim (fun i ↦ lin (Ξ a i)) X)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [ψ, algebraMap_eq]
      · intro i
        cases i with
        | inl i => simpa [ψ] using hxi a i
        | inr i => simp [ψ]
    exact congrArg (fun H : BiPoly d →+* RPoly d ↦ H F) he
  have ht : (template A deg).map (eval y) = C (4 * ε) - lin w ^ 2 := by
    simp only [template, Fin.getElem_fin, map_add, map_sum, map_mul, hgplain, hgslot, hinst]
    simp only [embedCoeff, MvPolynomial.map_map]
    have he : (eval y).comp (MvPolynomial.C : ℝ →+* NPoly) = RingHom.id ℝ := by
      ext r
      simp
    simp only [he, MvPolynomial.map_id]
    simpa only [map_mul] using (certificate_expansion A Ξ K hq).symm
  have htarg : (target (d := d) ε).map (eval y) = C (4 * ε) - lin w ^ 2 := by
    simp [target, lin, hy]
  have hcoef : ∀ μ, eval y (coefficient A deg ε μ) = 0 := by
    intro μ
    have hz : (target (d := d) ε - template A deg).map (eval y) = 0 := by
      rw [map_sub, ht, htarg, sub_self]
    have := congrArg (fun p : RPoly d ↦ p.coeff μ) hz
    simpa only [coeff_map, coefficient, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using this
  refine ⟨y, hy, ?_⟩
  intro f hf
  simp only [nestedSystem, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap] at hf
  rcases hf with (hf | hf) | hf
  · rcases hf with rfl | rfl
    · simp only [map_sub, map_sum, map_pow, eval_X, map_one]
      have hs : (∑ i : Fin d, y i.val ^ 2) = 1 := by
        simpa [sqnorm, dotProduct, pow_two, hy] using hw
      rw [hs]
      norm_num
    · simp only [map_sub, map_sum, map_pow, eval_X, map_one]
      have hs : (∑ i : Fin d, y i.val ^ 2) = 1 := by
        simpa [sqnorm, dotProduct, pow_two, hy] using hw
      rw [hs]
      norm_num
  · obtain ⟨μ, _, hf⟩ := hf
    rcases hf with rfl | rfl
    · rw [hcoef]
    · rw [map_neg, hcoef]
      norm_num
  · subst f
    simpa only [map_sub, eval_C, map_sum, map_pow, eval_X] using sub_nonneg.2 hball

private theorem specialize_embed (z : Fin d → NPoly) (f : RPoly d) :
    aeval z (embedCoeff f) = aeval z f := by
  simp only [embedCoeff, aeval_def, eval₂_map, algebraMap_eq]
  rfl

private theorem gram_specialize (z : Fin d → NPoly) (start e deg : ℕ)
    (hd : ∀ i, (z i).totalDegree ≤ 1)
    (hn : ∀ i, SoS.coeffNorm1 (z i) ≤ (d + 1 : ℝ)) (he : e ≤ deg) :
    SoS.IsSOS (aeval z (gram start (monos d e))) ∧
    (aeval z (gram start (monos d e))).totalDegree ≤ 2 * (e + 1) ∧
    SoS.coeffNorm1 (aeval z (gram start (monos d e))) ≤ ((d + 1 : ℝ) ^ deg) ^ 5 := by
  classical
  let L := monos d e
  have hb : (1 : ℝ) ≤ d + 1 := by have := Nat.cast_nonneg (α := ℝ) d; linarith
  have hm (μ : Fin d →₀ ℕ) :
      aeval z (monomial μ (1 : NPoly)) = aeval z (monomial μ (1 : ℝ)) := by
    simp [aeval_monomial, algebraMap_eq]
  have hmd (a : Fin L.length) :
      (aeval z (monomial L[a] (1 : NPoly))).totalDegree ≤ e := by
    rw [hm]
    exact (SoS.totalDegree_aeval_le z hd _).trans (by
      simpa only [mul_one] using
        (totalDegree_monomial_le L[a] (1 : ℝ)).trans
          (mem_monos.1 (List.getElem_mem a.isLt)))
  have hmn (a : Fin L.length) :
      SoS.coeffNorm1 (aeval z (monomial L[a] (1 : NPoly))) ≤ (d + 1 : ℝ) ^ e := by
    rw [hm]
    refine (SoS.coeffNorm1_aeval_le z hb hn _).trans ?_
    rw [SoS.coeffNorm1_monomial, abs_one, one_mul]
    exact pow_le_pow_right₀ hb
      ((totalDegree_monomial_le L[a] (1 : ℝ)).trans
        (mem_monos.1 (List.getElem_mem a.isLt)))
  have hid : aeval z (gram start L) =
      ∑ c : Fin L.length, (∑ a : Fin L.length,
        X (start + a * L.length + c) * aeval z (monomial L[a] (1 : NPoly))) ^ 2 := by
    simp [gram]
  rw [show monos d e = L from rfl, hid]
  refine ⟨SoS.IsSOS.sum _ (fun c _ ↦ SoS.IsSOS.sq _), ?_, ?_⟩
  · apply totalDegree_finsetSum_le
    intro c _
    apply (totalDegree_pow _ _).trans
    apply Nat.mul_le_mul_left
    apply totalDegree_finsetSum_le
    intro a _
    exact (totalDegree_mul _ _).trans (by have := hmd a; simp only [totalDegree_X]; omega)
  · have hi (c : Fin L.length) : SoS.coeffNorm1
        (∑ a : Fin L.length, X (start + a * L.length + c) *
          aeval z (monomial L[a] (1 : NPoly))) ≤ L.length * (d + 1 : ℝ) ^ e := by
      refine (SoS.coeffNorm1_sum_le _ _).trans ?_
      calc
        _ ≤ ∑ _a : Fin L.length, (d + 1 : ℝ) ^ e := by
          apply Finset.sum_le_sum
          intro a _
          exact (SoS.coeffNorm1_mul_le _ _).trans (by
            rw [SoS.coeffNorm1_X, one_mul]
            exact hmn a)
        _ = _ := by simp
    have hN : (L.length : ℝ) ≤ (d + 1 : ℝ) ^ deg := by
      exact_mod_cast (monos_length_le d e).trans
        (Nat.pow_le_pow_right (by omega) he)
    have hpow : (d + 1 : ℝ) ^ e ≤ (d + 1 : ℝ) ^ deg :=
      pow_le_pow_right₀ hb he
    calc
      _ ≤ ∑ _c : Fin L.length, (L.length * (d + 1 : ℝ) ^ e) ^ 2 := by
        refine (SoS.coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun c _ ↦ ?_)
        exact (SoS.coeffNorm1_pow_le _ _).trans
          (pow_le_pow_left₀ (SoS.coeffNorm1_nonneg _) (hi c) _)
      _ = L.length * (L.length * (d + 1 : ℝ) ^ e) ^ 2 := by simp
      _ ≤ (d + 1 : ℝ) ^ deg * ((d + 1 : ℝ) ^ deg * (d + 1 : ℝ) ^ deg) ^ 2 := by
        gcongr
      _ = _ := by ring

private theorem gram_coeff_degree (start e : ℕ) :
    NestedAux.CoeffDegree (gram (d := d) start (monos d e)) 2 := by
  apply NestedAux.CoeffDegree.sum
  intro c _
  apply NestedAux.CoeffDegree.pow (n := 1) (k := 2)
  apply NestedAux.CoeffDegree.sum
  intro a _
  have h₁ : NestedAux.CoeffDegree
      (C (X (start + a * (monos d e).length + c)) : Template d) 1 := by
    simpa using NestedAux.CoeffDegree.const (σ := Fin d)
      (X (start + a * (monos d e).length + c) : NPoly)
  have h₂ : NestedAux.CoeffDegree (monomial (monos d e)[a] (1 : NPoly)) 0 := by
    simpa using NestedAux.CoeffDegree.monomial (monos d e)[a] (1 : NPoly)
  simpa using h₁.mul h₂

private theorem coefficient_degree (A : FamilySystem d) (deg : ℕ) (ε : ℝ)
    (μ : Fin d →₀ ℕ) : (coefficient A deg ε μ).totalDegree ≤ outerDegree A := by
  have htwo : 2 ≤ outerDegree A := by unfold outerDegree; omega
  have hF : ∀ F ∈ A.families, F.totalDegree + 2 ≤ outerDegree A := by
    intro F hF
    have hmax : ∀ (L : List ℕ) (n : ℕ), ∀ x ∈ L, x ≤ L.foldl max n := by
      intro L
      induction L with
      | nil => simp
      | cons a L ih =>
        intro n x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · have hh : ∀ (L : List ℕ) (n : ℕ), n ≤ L.foldl max n := by
            intro L
            induction L with
            | nil => simp
            | cons a L ih =>
              intro n
              exact (le_max_left _ _).trans (ih (max _ _))
          exact (le_max_right n x).trans (hh L (max n x))
        · exact ih _ _ hx
    have := hmax (A.families.map totalDegree) 0 F.totalDegree (List.mem_map.2 ⟨F, hF, rfl⟩)
    unfold outerDegree
    omega
  have hxi (a i : ℕ) : NestedAux.CoeffDegree (xiLin A deg a i) 1 := by
    apply NestedAux.CoeffDegree.sum
    intro j _
    have h₁ := NestedAux.CoeffDegree.const (σ := Fin d)
      (X (slotOffset A deg a +
        familySize A deg (A.slots[a]?.map Fin.val |>.getD 0) ^ 2 + i * d + j) : NPoly)
    have h₂ : NestedAux.CoeffDegree (X j : Template d) 0 := by
      simpa only [MvPolynomial.X, totalDegree_one] using
        NestedAux.CoeffDegree.monomial (Finsupp.single j 1) (1 : NPoly)
    simpa using h₁.mul h₂
  have hembed (f : RPoly d) : NestedAux.CoeffDegree (embedCoeff f) 0 := by
    intro ν
    simp only [embedCoeff, coeff_map, totalDegree_C]
    exact le_rfl
  have ht : NestedAux.CoeffDegree (template A deg) (outerDegree A) := by
    apply NestedAux.CoeffDegree.add
    · apply NestedAux.CoeffDegree.sum
      intro j _
      exact ((gram_coeff_degree _ _).mul (hembed _)).mono (by omega)
    · apply NestedAux.CoeffDegree.sum
      intro a _
      have hf := NestedAux.CoeffDegree.eval_map
        (Sum.elim (fun i : Fin d ↦ xiLin A deg a i.val) X)
        (n := 1) (fun i ↦ by
          cases i with
          | inl i => exact hxi _ _
          | inr i =>
            exact (show NestedAux.CoeffDegree (X i : Template d) 0 by
              simpa only [MvPolynomial.X, totalDegree_one] using
                NestedAux.CoeffDegree.monomial (Finsupp.single i 1) (1 : NPoly)).mono
                  (by omega)) A.families[A.slots[a]]
      simp only [Fin.getElem_fin] at hf
      exact ((gram_coeff_degree _ _).mul hf).mono (by
        have hdegree := hF _ (List.getElem_mem (l := A.families) (A.slots[a]).isLt)
        simp only [Fin.getElem_fin] at hdegree
        omega)
  have htarget : NestedAux.CoeffDegree (target (d := d) ε) 2 := by
    apply NestedAux.CoeffDegree.sub
    · exact (show NestedAux.CoeffDegree (C (C (4 * ε) : NPoly) : Template d) 0 by
        simpa only [totalDegree_C] using
          NestedAux.CoeffDegree.const (σ := Fin d) (C (4 * ε) : NPoly)).mono
          (by omega)
    · apply NestedAux.CoeffDegree.pow (n := 1) (k := 2)
      apply NestedAux.CoeffDegree.sum
      intro i _
      have h₁ := NestedAux.CoeffDegree.const (σ := Fin d) (X i.val : NPoly)
      have h₂ : NestedAux.CoeffDegree (X i : Template d) 0 := by
        simpa only [MvPolynomial.X, totalDegree_one] using
          NestedAux.CoeffDegree.monomial (Finsupp.single i 1) (1 : NPoly)
      simpa using h₁.mul h₂
  exact (htarget.mono htwo |>.sub ht) μ

private def uVar (i : Fin d) : NPoly := X i.val

private def projectedVar (P : Mat d) (i : Fin d) : NPoly :=
  ∑ j : Fin d, C (P i j) * uVar j

private theorem projected_degree (P : Mat d) (i : Fin d) :
    (projectedVar P i).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by simp [uVar])

private theorem projected_norm (P : Mat d) (hp : Projection P) (i : Fin d) :
    SoS.coeffNorm1 (projectedVar P i) ≤ (d : ℝ) + 1 := by
  calc
    _ ≤ ∑ j : Fin d, |P i j| := by
      refine (SoS.coeffNorm1_sum_le _ _).trans ?_
      simp only [uVar, SoS.coeffNorm1_C_mul, SoS.coeffNorm1_X, mul_one]
      exact le_rfl
    _ ≤ ∑ _j : Fin d, (1 : ℝ) :=
      Finset.sum_le_sum fun j _ ↦ projection_entry P hp i j
    _ ≤ _ := by simp

private theorem specialize_aeval {σ : Type*} (z : Fin d → NPoly)
    (ψ : σ → Template d) (f : MvPolynomial σ ℝ) :
    aeval z (aeval ψ (f.map (MvPolynomial.C : ℝ →+* NPoly))) =
      aeval (fun i ↦ aeval z (ψ i)) f := by
  have he : (((aeval z).toRingHom.comp (aeval ψ).toRingHom).comp
      (map (MvPolynomial.C : ℝ →+* NPoly))) =
        (aeval (fun i ↦ aeval z (ψ i))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [algebraMap_eq]
    · intro i
      simp
  exact congrArg (fun H : MvPolynomial σ ℝ →+* NPoly ↦ H f) he

private theorem lift_ball {σ : Type*} (A : FamilySystem d) (deg : ℕ) (ε Bd M β : ℝ)
    (b g : MvPolynomial σ ℝ) (k e : ℕ) (φ : σ → NPoly)
    (h : SoS.DerivesNq [b] k M 1 g)
    (hd : ∀ i, (φ i).totalDegree ≤ e) (hβ : 1 ≤ β)
    (hn : ∀ i, SoS.coeffNorm1 (φ i) ≤ β)
    (hb : aeval φ b = 1 - ∑ i : Fin d, (X i.val : NPoly) ^ 2) :
    SoS.DerivesNq (nestedSystem A deg ε Bd) (k * e) (2 * M * β ^ k) 1 (aeval φ g) := by
  have ht := NestedAux.aevalNq h φ hd hβ hn
  have htrans : ∀ f ∈ [b].map (aeval φ),
      SoS.DerivesNq (nestedSystem A deg ε Bd) f.totalDegree 1 1 f := by
    intro f hf
    have he : f = aeval φ b := by simpa using hf
    subst f
    refine SoS.DerivesNq.of_mem ?_ le_rfl le_rfl (by omega)
    rw [hb]
    simp [nestedSystem]
  convert ht.trans htrans using 1
  simp
  ring

private theorem template_nonneg (A : FamilySystem d) (deg : ℕ) (ε Bd M : ℝ)
    (P : Mat d) (hA : A.Valid deg) (hp : Projection P) (hM : 0 ≤ M)
    (hplain : ∀ f ∈ A.plain, SoS.DerivesNq ball f.totalDegree M 1 (subst P f))
    (hfamily : ∀ F ∈ A.families, SoS.DerivesNq [1 - liftV nsq] F.totalDegree M 1
      (substV P F)) :
    SoS.DerivesNq (nestedSystem A deg ε Bd) (solverDegree A deg)
      ((A.plain.length + 1 + A.slots.length) *
        (2 * (M + 1) * (d + 1 : ℝ) ^ (2 * deg) * ((d + 1 : ℝ) ^ deg) ^ 5)) 1
      (aeval (projectedVar P) (template A deg)) := by
  classical
  let z := projectedVar P
  let B := 2 * (M + 1) * (d + 1 : ℝ) ^ (2 * deg)
  let G := ((d + 1 : ℝ) ^ deg) ^ 5
  have hb : (1 : ℝ) ≤ d + 1 := by have := Nat.cast_nonneg (α := ℝ) d; linarith
  have hβ : (1 : ℝ) ≤ (d + 1 : ℝ) ^ 2 := one_le_pow₀ hb
  have hzdeg : ∀ i, (z i).totalDegree ≤ 1 := projected_degree P
  have hznorm : ∀ i, SoS.coeffNorm1 (z i) ≤ d + 1 := projected_norm P hp
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsolver : 2 * deg + 2 ≤ solverDegree A deg := by
    have : 2 ≤ outerDegree A := by unfold outerDegree; omega
    unfold solverDegree
    omega
  have hnorm (k : ℕ) (hk : k ≤ deg) :
      2 * (M + 1) * ((d + 1 : ℝ) ^ 2) ^ k ≤ B := by
    dsimp [B]
    rw [← pow_mul]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hb (Nat.mul_le_mul_left 2 hk)) (by positivity)
  have hplain' : ∀ f ∈ constraintsWithOne A,
      SoS.DerivesNq (nestedSystem A deg ε Bd) f.totalDegree B 1 (aeval z (embedCoeff f)) := by
    intro f hf
    have hfd : f.totalDegree ≤ deg := by
      rcases List.mem_cons.1 hf with rfl | hf
      · simp
      · exact hA.2.1 _ hf
    have ht : SoS.DerivesNq ball f.totalDegree (M + 1) 1 (subst P f) := by
      rcases List.mem_cons.1 hf with rfl | hf
      · simpa [subst] using SoS.DerivesNq.ofIsSOS (q := 1) ball SoS.IsSOS.one
          (k := 0) (by simp) (by rw [SoS.coeffNorm1_one]; linarith)
      · exact (hplain f hf).mono le_rfl (by linarith)
    have hs := lift_ball A deg ε Bd (M + 1) ((d + 1 : ℝ) ^ 2)
      (1 - nsq) (subst P f) f.totalDegree 1 uVar ht
      (fun i ↦ by simp [uVar]) hβ (fun i ↦ by simpa [uVar, SoS.coeffNorm1_X] using hβ)
      (by simp [nsq, uVar])
    refine (hs.mono (by simp) (hnorm _ hfd)).congr ?_
    rw [specialize_embed, subst, comp_aeval_apply]
    simp only [lin, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq]
    rfl
  have hslot (a : Fin A.slots.length) :
      SoS.DerivesNq (nestedSystem A deg ε Bd)
        (2 * A.families[(A.slots[a.val]).val].totalDegree) B 1
        (aeval z (aeval (Sum.elim (fun i : Fin d ↦ xiLin A deg a i.val) X)
          (A.families[(A.slots[a.val]).val].map (MvPolynomial.C : ℝ →+* NPoly)))) := by
    let ψ : Fin d ⊕ Fin d → NPoly :=
      Sum.elim (fun i ↦ aeval z (xiLin A deg a i.val)) uVar
    have hψdeg : ∀ i, (ψ i).totalDegree ≤ 2 := by
      intro i
      cases i with
      | inl i =>
        simp only [ψ, Sum.elim_inl, xiLin, map_sum, map_mul, aeval_C, aeval_X,
          Algebra.algebraMap_self, RingHom.id_apply]
        apply totalDegree_finsetSum_le
        intro j _
        exact (totalDegree_mul _ _).trans (by have := hzdeg j; simp; omega)
      | inr i => simp [ψ, uVar]
    have hψnorm : ∀ i, SoS.coeffNorm1 (ψ i) ≤ (d + 1 : ℝ) ^ 2 := by
      intro i
      cases i with
      | inl i =>
        simp only [ψ, Sum.elim_inl, xiLin, map_sum, map_mul, aeval_C, aeval_X,
          Algebra.algebraMap_self, RingHom.id_apply]
        calc
          _ ≤ ∑ _j : Fin d, (d + 1 : ℝ) := by
            refine (SoS.coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
            exact (SoS.coeffNorm1_mul_le _ _).trans (by
              rw [SoS.coeffNorm1_X, one_mul]
              exact hznorm j)
          _ ≤ _ := by simp; nlinarith [Nat.cast_nonneg (α := ℝ) d]
      | inr i => simpa [ψ, uVar, SoS.coeffNorm1_X] using hβ
    have hf := hfamily _ (List.getElem_mem (l := A.families) (A.slots[a]).isLt)
    simp only [Fin.getElem_fin] at hf
    have ht := lift_ball A deg ε Bd M ((d + 1 : ℝ) ^ 2) (1 - liftV nsq)
      _ _ 2 ψ hf hψdeg hβ hψnorm (by simp [liftV, nsq, ψ, uVar])
    refine (ht.mono (by omega) ?_).congr ?_
    · refine (mul_le_mul_of_nonneg_right (by linarith : 2 * M ≤ 2 * (M + 1))
        (pow_nonneg (by positivity) _)).trans (hnorm _ (hA.2.2 _
          (List.getElem_mem (l := A.families) (A.slots[a]).isLt)))
    · rw [substV, comp_aeval_apply, specialize_aeval]
      congr 2
      funext i
      cases i with
      | inl i => simp [ψ]
      | inr i => simp [ψ, liftV, lin, projectedVar, uVar, z]
  have hpterms : ∀ j : Fin (A.plain.length + 1),
      SoS.DerivesNq (nestedSystem A deg ε Bd) (solverDegree A deg) (B * G) 1
        (aeval z (gram (plainOffset A deg j)
          (monos d ((deg - (constraintsWithOne A)[j.val].totalDegree) / 2)) *
            embedCoeff (constraintsWithOne A)[j.val])) := by
    intro j
    have hf := hplain' _ (List.getElem_mem (l := constraintsWithOne A) j.isLt)
    obtain ⟨hs, hd, hn⟩ := gram_specialize z (plainOffset A deg j)
      ((deg - (constraintsWithOne A)[j.val].totalDegree) / 2) deg hzdeg hznorm (by omega)
    have hfd : (constraintsWithOne A)[j.val].totalDegree ≤ deg := by
      rcases List.mem_cons.1 (List.getElem_mem (l := constraintsWithOne A) j.isLt) with he | he
      · have hzero := congrArg MvPolynomial.totalDegree he
        simp only [totalDegree_one] at hzero
        omega
      · exact hA.2.1 _ he
    refine ((hf.mulSOS hs).mono (M' := B * G) (by omega) ?_).congr
      (map_mul (aeval z) _ _).symm
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hn hB
  have hsterms : ∀ a : Fin A.slots.length,
      SoS.DerivesNq (nestedSystem A deg ε Bd) (solverDegree A deg) (B * G) 1
        (aeval z (gram (slotOffset A deg a)
          (monos d ((deg - A.families[(A.slots[a.val]).val].totalDegree) / 2)) *
          aeval (Sum.elim (fun i : Fin d ↦ xiLin A deg a i.val) X)
            (A.families[(A.slots[a.val]).val].map (MvPolynomial.C : ℝ →+* NPoly)))) := by
    intro a
    obtain ⟨hs, hd, hn⟩ := gram_specialize z (slotOffset A deg a)
      ((deg - A.families[(A.slots[a.val]).val].totalDegree) / 2) deg hzdeg hznorm (by omega)
    have hfd := hA.2.2 _ (List.getElem_mem (l := A.families) (A.slots[a]).isLt)
    simp only [Fin.getElem_fin] at hfd
    refine (((hslot a).mulSOS hs).mono (M' := B * G) (by omega) ?_).congr
      (map_mul (aeval z) _ _).symm
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hn hB
  have ht := (SoS.DerivesNq.sum Finset.univ (fun j _ ↦ hpterms j)).add
    (SoS.DerivesNq.sum Finset.univ (fun a _ ↦ hsterms a))
  refine (ht.mono le_rfl ?_).congr ?_
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [B, G]
    push_cast
    ring_nf
    exact le_rfl
  · simp only [template, map_add, map_sum, Fin.getElem_fin, z]

private theorem matching_nonneg (A : FamilySystem d) (deg : ℕ) (ε Bd : ℝ)
    (hA : A.Valid deg) (z : Fin d → NPoly)
    (hd : ∀ i, (z i).totalDegree ≤ 1)
    (hn : ∀ i, SoS.coeffNorm1 (z i) ≤ d + 1) :
    SoS.DerivesNq (nestedSystem A deg ε Bd) (solverDegree A deg)
      ((d + 1 : ℝ) ^ deg * ((d + 1 : ℝ) ^ deg + 1) ^ 2) 1
      (aeval z (target ε - template A deg)) := by
  classical
  let r : (Fin d →₀ ℕ) → NPoly := fun μ ↦ aeval z (monomial μ (1 : ℝ))
  let b := (d + 1 : ℝ) ^ deg
  have hb : (1 : ℝ) ≤ d + 1 := by have := Nat.cast_nonneg (α := ℝ) d; linarith
  have hsolver : 2 * deg + outerDegree A ≤ solverDegree A deg := by
    unfold solverDegree
    omega
  have hr (μ : Fin d →₀ ℕ) (hμ : μ ∈ monos d deg) :
      (r μ).totalDegree ≤ deg ∧ SoS.coeffNorm1 (r μ) ≤ b := by
    have hm := (totalDegree_monomial_le μ (1 : ℝ)).trans (mem_monos.1 hμ)
    constructor
    · exact (SoS.totalDegree_aeval_le z hd _).trans (by simpa using hm)
    · refine (SoS.coeffNorm1_aeval_le z hb hn _).trans ?_
      rw [SoS.coeffNorm1_monomial, abs_one, one_mul]
      exact pow_le_pow_right₀ hb hm
  have ht : ∀ j : Fin (monos d deg).length,
      SoS.DerivesNq (nestedSystem A deg ε Bd) (solverDegree A deg) ((b + 1) ^ 2) 1
        (r (monos d deg)[j.val] * coefficient A deg ε (monos d deg)[j.val]) := by
    intro j
    have hμ := List.getElem_mem (l := monos d deg) j.isLt
    have hp : coefficient A deg ε (monos d deg)[j.val] ∈ nestedSystem A deg ε Bd := by
      simp only [nestedSystem, List.mem_append]
      exact Or.inl (Or.inr (List.mem_flatMap.2 ⟨(monos d deg)[j.val], hμ, by simp⟩))
    have hm : -coefficient A deg ε (monos d deg)[j.val] ∈ nestedSystem A deg ε Bd := by
      simp only [nestedSystem, List.mem_append]
      exact Or.inl (Or.inr (List.mem_flatMap.2 ⟨(monos d deg)[j.val], hμ, by simp⟩))
    have hh := NestedAux.mul_eq hp hm (r (monos d deg)[j.val])
    exact hh.mono (by
      have := coefficient_degree A deg ε (monos d deg)[j.val]
      have := (hr _ hμ).1
      omega) (pow_le_pow_left₀ (by linarith [SoS.coeffNorm1_nonneg (r (monos d deg)[j.val])])
        (by linarith [(hr _ hμ).2]) _)
  have hs := SoS.DerivesNq.sum Finset.univ (fun j _ ↦ ht j)
  have he : aeval z (target ε - template A deg) =
      ∑ j : Fin (monos d deg).length,
        r (monos d deg)[j.val] * coefficient A deg ε (monos d deg)[j.val] := by
    have hid := congrArg (aeval z) (nested_identity A deg ε hA)
    rw [← Fin.sum_univ_fun_getElem (monos d deg)
      (fun μ ↦ monomial μ (coefficient A deg ε μ)), map_sum] at hid
    refine hid.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
    simp [r, aeval_monomial, mul_comm]
  refine (hs.mono le_rfl ?_).congr he.symm
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast monos_length_le d deg

private theorem quad_add (P Q : Mat d) : quad (P + Q) = quad P + quad Q := by
  simp [quad, Matrix.add_apply, C_add, add_mul, Finset.sum_add_distrib]

private theorem quad_one : quad (1 : Mat d) = nsq := by
  simp [quad, nsq, Matrix.one_apply, pow_two, apply_ite, ite_mul]

/-- Complement feasibility gives the corrected concentration certificate. -/
theorem nested_concentration
    (A : FamilySystem d) (deg : ℕ) (ε Bd M : ℝ) (R : Mat d)
    (hA : A.Valid deg) (hR : Projection R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : A.FeasibleComplement R M) :
    SoS.DerivesNq (nestedSystem A deg ε Bd) (solverDegree A deg)
      (nestedNorm A deg ε M) 1
      (rename Fin.val (quad R) - C (1 - 2 * Real.sqrt ε)) := by
  classical
  have hM : 0 ≤ M := (h.1 _ hA.1).nonneg
  let P : Mat d := 1 - R
  have hp : Projection P := by
    constructor
    · simp [P, transpose_sub, hR.1]
    · simp only [P, sub_mul, mul_sub, one_mul, mul_one, hR.2]
      abel
  let z := projectedVar P
  let x : NPoly := ∑ i : Fin d, uVar i * z i
  have hxdeg : x.totalDegree ≤ 2 := by
    apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans (by
      have hz : (z i).totalDegree ≤ 1 := projected_degree P i
      simp only [uVar, totalDegree_X]
      omega)
  have hxnorm : SoS.coeffNorm1 x ≤ (d + 1 : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin d, (d + 1 : ℝ) := by
        refine (SoS.coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        exact (SoS.coeffNorm1_mul_le _ _).trans (by
          rw [uVar, SoS.coeffNorm1_X, one_mul]
          exact projected_norm P hp i)
      _ ≤ _ := by simp; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hxquad : x = rename Fin.val (quad P) := by
    simp only [x, z, projectedVar, uVar, quad, map_sum, map_mul, rename_C, rename_X,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsplit : rename Fin.val (quad R) + x = ∑ i : Fin d, (X i.val : NPoly) ^ 2 := by
    rw [hxquad, ← map_add, ← quad_add]
    have he : R + P = 1 := by dsimp [P]; abel
    rw [he, quad_one]
    simp [nsq]
  have ht := template_nonneg A deg ε Bd M P hA hp hM h.1 h.2
  have hi := matching_nonneg A deg ε Bd hA z (projected_degree P) (projected_norm P hp)
  have hs := (ht.add hi).congr (show aeval z (template A deg) +
      aeval z (target ε - template A deg) = C (4 * ε) - x ^ 2 by
    rw [map_sub]
    have he : aeval z (target (d := d) ε) = C (4 * ε) - x ^ 2 := by
      simp only [target, map_sub, map_pow, map_sum, map_mul, aeval_C, aeval_X,
        Algebra.algebraMap_self, RingHom.id_apply, x, uVar]
    rw [he]
    ring)
  have hsq : (2 * Real.sqrt ε) ^ 2 = 4 * ε := by
    nlinarith [Real.sq_sqrt hε.le]
  have hs' := hs.congr (show C (4 * ε) - x ^ 2 = C ((2 * Real.sqrt ε) ^ 2) - x ^ 2 by
    rw [hsq])
  have hroot := hs'.sqrt_sub (by positivity : 0 < 2 * Real.sqrt ε)
  have hdeg : 2 * x.totalDegree ≤ solverDegree A deg := by
    by_cases hd : d = 0
    · subst d
      simp [x]
    · have htwo := valid_degree A deg hA ⟨0, by omega⟩
      have : 2 ≤ outerDegree A := by unfold outerDegree; omega
      unfold solverDegree
      omega
  have hnorm : (SoS.coeffNorm1 x + 2 * Real.sqrt ε) ^ 2 ≤
      ((d + 1 : ℝ) ^ 2 + 2) ^ 2 := by
    have hsqrt : Real.sqrt ε ≤ 1 := by
      nlinarith [Real.sq_sqrt hε.le, Real.sqrt_nonneg ε]
    apply pow_le_pow_left₀ (add_nonneg (SoS.coeffNorm1_nonneg x)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg ε)))
    linarith
  have hfinal := (hroot.mono (max_le le_rfl hdeg) le_rfl).add
    ((nested_sphere A deg ε Bd).1.mono (by
      have : 2 ≤ outerDegree A := by unfold outerDegree; omega
      unfold solverDegree
      omega) le_rfl)
  refine (hfinal.mono le_rfl ?_).congr ?_
  · dsimp only [nestedNorm]
    rw [show 2 * (2 * Real.sqrt ε) = 4 * Real.sqrt ε by ring]
    exact add_le_add (div_le_div_of_nonneg_right (add_le_add le_rfl hnorm)
      (by positivity)) le_rfl
  · have he := hsplit
    simp only [map_sub, map_mul, map_one]
    linear_combination -he

/-- The nested encoding has polynomially many variables and constraints. -/
theorem nested_size
    (A : FamilySystem d) (deg : ℕ) (ε Bd : ℝ) :
    nestedVars A deg ≤ d + (A.plain.length + 1 + A.slots.length) * (d + 1) ^ deg +
      A.slots.length * d ^ 2 ∧
    (nestedSystem A deg ε Bd).length ≤ 2 * (d + 1) ^ deg + 3 := by
  constructor
  · have hp := range_sum_le (fun i ↦ gramSize A deg i ^ 2)
      (A.plain.length + 1) ((d + 1) ^ deg) (fun i _ ↦ gramSize_sq_le A deg i)
    have hs := range_sum_le
      (fun i ↦ familySize A deg (A.slots[i]?.map Fin.val |>.getD 0) ^ 2 + d ^ 2)
      A.slots.length ((d + 1) ^ deg + d ^ 2)
      (fun i _ ↦ Nat.add_le_add_right (familySize_sq_le A deg _) _)
    dsimp [nestedVars, slotOffset, plainOffset]
    calc
      _ ≤ d + (A.plain.length + 1) * (d + 1) ^ deg +
          A.slots.length * ((d + 1) ^ deg + d ^ 2) := by omega
      _ = _ := by ring
  · have hm := monos_length_le d deg
    have hl : ∀ L : List (Fin d →₀ ℕ),
        (L.flatMap fun μ ↦ [coefficient A deg ε μ, -coefficient A deg ε μ]).length =
          2 * L.length := by
      intro L
      induction L with
      | nil => simp
      | cons μ L ih => simp [ih]; omega
    simp only [nestedSystem, List.length_append, List.length_cons, List.length_nil, hl]
    omega

end

end ABBKS26.Rounding
