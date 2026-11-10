module

public import ABBKS26.Assembly.ExecRoundCertificatesAuxGeometry

/-! Analytic interpretation of the concrete greedy steps. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RoundCertificates.Capture

open Common Rounding RoundProgram Matrix FrameAux.Linear
open scoped BigOperators

noncomputable section

def columns (a : RoundArgs) (B : Points) : Matrix (Fin a.2.1) (Fin B.length) ℝ :=
  fun i j ↦ (vectorOf a.2.1 B[j] i : ℝ)

theorem proj_columns (a : RoundArgs) (B : Points) :
    (output a B).proj = DetRoundAux.frameProj (columns a B) := by
  have hlen : (output a B).basis.length = B.length := by simp [output]
  let e := finCongr hlen
  have hm : (fun (i : Fin a.2.1) (j : Fin (output a B).basis.length) ↦
      ((output a B).basis[j] i : ℝ)) = (columns a B).submatrix id e := by
    ext i j
    change ((B.map (vectorOf a.2.1))[j.val] i : ℝ) = _
    rw [List.getElem_map]
    rfl
  change DetRoundAux.frameProj _ = _
  rw [hm]
  unfold DetRoundAux.frameProj
  have hg : (columns a B)ᵀ.submatrix e id * (columns a B).submatrix id e =
      ((columns a B)ᵀ * columns a B).submatrix e e :=
    submatrix_mul_equiv _ _ e (Equiv.refl _) e
  rw [transpose_submatrix, hg, inv_submatrix_equiv,
    submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]

theorem gram_ne_zero (a : RoundArgs) (B : Points) (hB : GoodBasis a B) :
    ((columns a B)ᵀ * columns a B).det ≠ 0 := by
  intro hz
  have hp : (output a B).proj = 0 := by
    rw [proj_columns, DetRoundAux.frameProj, Matrix.nonsing_inv_apply_not_isUnit]
    · simp
    · simpa only [isUnit_iff_ne_zero] using not_not_intro hz
  have hr := (Geometry.basis_geometry a B hB).2.1
  rw [hp, rank_zero] at hr
  have hd := Matrix.det_eq_one_of_card_eq_zero
    (A := (columns a B)ᵀ * columns a B) (by simpa using hr.symm)
  exact zero_ne_one (hz.symm.trans hd)

theorem fixes_columns (a : RoundArgs) (B : Points) (hB : GoodBasis a B) :
    (output a B).proj * columns a B = columns a B := by
  rw [proj_columns]
  exact (DetRoundAux.frameProj_spec _ (gram_ne_zero a B hB)).2.2

theorem fixes_mem (a : RoundArgs) (B : Points) (hB : GoodBasis a B)
    (v : Vector) (hv : v ∈ B) :
    InRange (output a B).proj (fun i ↦ (vectorOf a.2.1 v i : ℝ)) := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hv
  funext i
  exact congrArg (fun A ↦ A i ⟨j, hj⟩) (fixes_columns a B hB)

theorem fixes_of_fixes_columns (a : RoundArgs) (B : Points) (T : Mat a.2.1)
    (hT : ∀ v ∈ B, InRange T (fun i ↦ (vectorOf a.2.1 v i : ℝ))) :
    T * (output a B).proj = (output a B).proj := by
  have hb : T * columns a B = columns a B := by
    ext i j
    exact congrFun (hT B[j] (List.getElem_mem j.isLt)) i
  rw [proj_columns]
  unfold DetRoundAux.frameProj
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hb]

theorem prefix_range (a : RoundArgs) (B D : Points) (hD : GoodBasis a D)
    (hBD : B <+: D) : ∀ x, InRange (output a B).proj x →
      InRange (output a D).proj x := by
  have h := fixes_of_fixes_columns a B (output a D).proj
    (fun v hv ↦ fixes_mem a D hD v (hBD.sublist.subset hv))
  intro x hx
  change (output a B).proj *ᵥ x = x at hx
  change (output a D).proj *ᵥ x = x
  rw [← hx, mulVec_mulVec, h]

theorem projection_snoc (a : RoundArgs) (B : Points) (v : Vector)
    (hB : GoodBasis a B) (hv : acceptable a B v) (hg : OnGrid a v) :
    let P := (output a B).proj
    let z := (1 - P) *ᵥ (fun i ↦ (vectorOf a.2.1 v i : ℝ))
    (output a (B ++ [v])).proj = P + (sqnorm z)⁻¹ • vecMulVec z z := by
  let P := (output a B).proj
  let Q := (output a (B ++ [v])).proj
  let w : Vec a.2.1 := fun i ↦ (vectorOf a.2.1 v i : ℝ)
  let z := (1 - P) *ᵥ w
  have hP : Projection P := (Geometry.basis_geometry a B hB).1
  have hQ : Projection Q := (Geometry.basis_geometry a (B ++ [v]) (.snoc hB hv hg)).1
  have hz : 0 < sqnorm z := by
    have h := hv.2.2.1
    have hh : (9 / 64 : ℝ) ≤ sqnorm z := by
      rw [← Geometry.residual_eq]
      have hh := Rat.cast_le (K := ℝ) |>.2 h
      norm_num at hh ⊢
      exact hh
    linarith
  have hPz : P *ᵥ z = 0 := by
    dsimp only [z]
    rw [mulVec_mulVec, mul_sub, mul_one, hP.2, sub_self, zero_mulVec]
  have hPQ : Q * P = P := fixes_of_fixes_columns a B Q (fun t ht ↦
    fixes_mem a (B ++ [v]) (.snoc hB hv hg) t (List.mem_append_left _ ht))
  have hQw : Q *ᵥ w = w :=
    fixes_mem a (B ++ [v]) (.snoc hB hv hg) v (by simp)
  have hQz : Q *ᵥ z = z := by
    dsimp only [z]
    rw [sub_mulVec, one_mulVec, mulVec_sub, hQw, mulVec_mulVec, hPQ]
  let T := P + (sqnorm z)⁻¹ • vecMulVec z z
  have hT : Tᵀ = T := by
    simp only [T, transpose_add, hP.1, transpose_smul, transpose_vecMulVec]
  have hQP : Q * T = T := by
    simp only [T, mul_add, hPQ, Matrix.mul_smul, mul_vecMulVec, hQz]
  have hTw : T *ᵥ w = w := by
    have hd : z ⬝ᵥ w = sqnorm z := by
      rw [show w = P *ᵥ w + z by simp [z, sub_mulVec]]
      rw [dotProduct_add, ← DetRoundAux.projection_dot P hP, hPz, zero_dotProduct]
      simp only [zero_add, sqnorm]
    rw [show T = P + (sqnorm z)⁻¹ • vecMulVec z z from rfl, add_mulVec,
      smul_mulVec, vecMulVec_mulVec, hd, op_smul_eq_smul, smul_smul,
      inv_mul_cancel₀ hz.ne', one_smul]
    simp [z, sub_mulVec]
  have hTP : T * P = P := by
    have hd : z ᵥ* P = 0 := by rw [← hP.1, vecMul_transpose, hPz]
    simp only [T, add_mul, hP.2, smul_mul, vecMulVec_mul, hd, vecMulVec_zero,
      smul_zero, add_zero]
  have hTQ : T * Q = Q := fixes_of_fixes_columns a (B ++ [v]) T (by
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · change T *ᵥ _ = _
      have hf := fixes_mem a B hB t ht
      change P *ᵥ _ = _ at hf
      rw [← hf, mulVec_mulVec, hTP]
    · have he : t = v := by simpa using ht
      subst t
      exact hTw)
  have he := congrArg Matrix.transpose hQP
  rw [transpose_mul, hT, hQ.1] at he
  exact hTQ.symm.trans he

theorem snoc_trace (a : RoundArgs) (B : Points) (v : Vector) (M : Mat a.2.1)
    (hB : GoodBasis a B) (hv : acceptable a B v) (hg : OnGrid a v) :
    let P := (output a B).proj
    let z := (1 - P) *ᵥ (fun i ↦ (vectorOf a.2.1 v i : ℝ))
    ((output a (B ++ [v])).proj * M).trace =
      (P * M).trace + qform M z / sqnorm z := by
  rw [projection_snoc a B v hB hv hg, add_mul, trace_add, smul_mul, trace_smul,
    vecMulVec_mul, trace_vecMulVec]
  congr 1
  rw [smul_eq_mul, qform, dotProduct_comm]
  rw [← dotProduct_mulVec]
  ring

theorem psd_abs_entries {d : ℕ} (M : Mat d) (hM : M.PosSemidef) :
    (∑ i, ∑ j, |M i j|) ≤ d * M.trace := by
  have hs : Mᵀ = M := by simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    using hM.1
  have hd (i j : Fin d) : 2 * |M i j| ≤ M i i + M j j := by
    have hp := hM.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
    have hm := hM.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
    have he : M j i = M i j := congrArg (fun A ↦ A i j) hs
    simp only [star_trivial, add_dotProduct, sub_dotProduct, mulVec_add, mulVec_sub,
      dotProduct_add, dotProduct_sub, single_dotProduct, one_mul, mulVec_single,
      op_smul_eq_smul, one_smul, col, transpose_apply, he] at hp hm
    rcases le_total 0 (M i j) with h | h
    · rw [abs_of_nonneg h]
      linarith
    · rw [abs_of_nonpos h]
      linarith
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
    Finset.sum_le_sum (s := Finset.univ) fun j _ ↦ hd i j
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  change _ ≤ d * ∑ i, M i i
  linarith

theorem qform_round_error {d : ℕ} (M : Mat d) (hM : M.PosSemidef)
    (v u : Vec d) (δ : ℝ) (hδ : 0 ≤ δ)
    (hv : ∀ i, |v i| ≤ 1) (hu : ∀ i, |u i| ≤ 1)
    (he : ∀ i, |v i - u i| ≤ δ) :
    |qform M v - qform M u| ≤ 2 * δ * d * M.trace := by
  have hp (i j : Fin d) : |v i * v j - u i * u j| ≤ 2 * δ := by
    calc
      _ = |(v i - u i) * v j + u i * (v j - u j)| := by congr 1; ring
      _ ≤ |v i - u i| * |v j| + |u i| * |v j - u j| := by
        simpa only [abs_mul] using abs_add_le ((v i - u i) * v j) (u i * (v j - u j))
      _ ≤ δ * 1 + 1 * δ := by gcongr <;> first | exact he _ | exact hv _ | exact hu _
      _ = _ := by ring
  have hex : qform M v - qform M u =
      ∑ i, ∑ j, M i j * (v i * v j - u i * u j) := by
    simp only [qform, mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hex]
  calc
    _ ≤ ∑ i, ∑ j, |M i j| * |v i * v j - u i * u j| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro i _
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun j ↦ M i j * (v i * v j - u i * u j)) Finset.univ
    _ ≤ ∑ i, ∑ j, |M i j| * (2 * δ) := by gcongr with i j; exact hp i j
    _ = (2 * δ) * ∑ i, ∑ j, |M i j| := by
      simp only [← Finset.sum_mul]
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (psd_abs_entries M hM) (by positivity : 0 ≤ 2 * δ)
      convert h using 1
      ring

theorem table_matrix (d : ℕ) (f : ℕ → ℕ → ℚ) :
    matrixOf d (table d f) = fun (i j : Fin d) ↦ f i j := by
  ext i j
  simp [matrixOf, table, i.isLt, j.isLt]

theorem multiply_matrix (d : ℕ) (A B : MatrixL) :
    matrixOf d (multiply d A B) = matrixOf d A * matrixOf d B := by
  rw [multiply, table_matrix]
  ext i j
  exact (sum_fin_eq_list (fun k : Fin d ↦ ent A i k * ent B k j)
    (fun k ↦ ent A i k * ent B k j) (fun _ ↦ rfl)).symm

theorem trace_matrix (d : ℕ) (A : MatrixL) : trace d A = (matrixOf d A).trace := by
  exact (sum_fin_eq_list (fun i : Fin d ↦ ent A i i)
    (fun i ↦ ent A i i) (fun _ ↦ rfl)).symm

theorem test_matrix (a : RoundArgs) (B : Points) (M : MatrixL) :
    (matrixOf a.2.1 (table a.2.1 fun i j ↦
      (if i = j then greedyThreshold a.2.2.1 a.2.2.2.1 else 0) -
        ent (multiply a.2.1 (multiply a.2.1 (complement a.2.1 B) M)
          (complement a.2.1 B)) i j)).map (algebraMap ℚ ℝ) =
      (greedyThreshold a.2.2.1 a.2.2.2.1 : ℝ) • (1 : Mat a.2.1) -
        (1 - (output a B).proj) * (matrixOf a.2.1 M).map (algebraMap ℚ ℝ) *
          (1 - (output a B).proj) := by
  have hm : (matrixOf a.2.1 (multiply a.2.1
      (multiply a.2.1 (complement a.2.1 B) M) (complement a.2.1 B))).map
        (algebraMap ℚ ℝ) = (1 - (output a B).proj) *
          (matrixOf a.2.1 M).map (algebraMap ℚ ℝ) * (1 - (output a B).proj) := by
    rw [multiply_matrix, multiply_matrix, Matrix.map_mul, Matrix.map_mul,
      Geometry.complement_eq]
  rw [← hm, table_matrix]
  ext i j
  change (((if i.val = j.val then greedyThreshold a.2.2.1 a.2.2.2.1 else 0) -
    ent (multiply a.2.1 (multiply a.2.1 (complement a.2.1 B) M)
      (complement a.2.1 B)) i j : ℚ) : ℝ) = _
  push_cast
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp [matrixOf, ent]
  · have hh : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
    simp [hij, hh, matrixOf, ent]

theorem precision_error (a : RoundArgs) :
    0 < (greedyThreshold a.2.2.1 a.2.2.2.1 : ℝ) ∧
      (a.2.1 + 1 : ℝ) / 2 ^ greedyPrecision a ≤
        greedyThreshold a.2.2.1 a.2.2.2.1 / 480 := by
  let θ := greedyThreshold a.2.2.1 a.2.2.2.1
  have hθ : 0 < θ := Bounds.threshold_pos a
  have hpow : (120 * (a.2.1 + 1 : ℚ) / θ) ≤
      2 ^ Nat.clog 2 ⌈120 * (a.2.1 + 1 : ℚ) / θ⌉₊ :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) _)
  have hb := (div_le_iff₀ hθ).1 hpow
  have hb' : 120 * (a.2.1 + 1 : ℝ) ≤
      (2 : ℝ) ^ Nat.clog 2 ⌈120 * (a.2.1 + 1 : ℚ) / θ⌉₊ * θ := by exact_mod_cast hb
  refine ⟨by exact_mod_cast hθ, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  dsimp only [greedyPrecision]
  rw [pow_add]
  norm_num
  dsimp only [θ] at hb'
  nlinarith

def pdTable (a : RoundArgs) (B : Points) (M : MatrixL) : MatrixL :=
  table a.2.1 fun i j ↦
    (if i = j then greedyThreshold a.2.2.1 a.2.2.2.1 else 0) -
      ent (multiply a.2.1 (multiply a.2.1 (complement a.2.1 B) M)
        (complement a.2.1 B)) i j

theorem pd_spec (a : RoundArgs) (B : Points) (M : MatrixL)
    (hB : GoodBasis a B) (hM : ((matrixOf a.2.1 M).map (algebraMap ℚ ℝ)).PosSemidef) :
    let P := (output a B).proj
    let N := (matrixOf a.2.1 M).map (algebraMap ℚ ℝ)
    let θ : ℝ := greedyThreshold a.2.2.1 a.2.2.2.1
    (SoS.PDTestRat.test (pdTable a B M) = none →
      Common.LE ((1 - P) * N * (1 - P)) (θ • (1 : Mat a.2.1))) ∧
    ∀ y, SoS.PDTestRat.test (pdTable a B M) = some y →
      ∃ w : Fin a.2.1 → ℤ, y = List.ofFn w ∧ w ≠ 0 ∧
        θ * sqnorm (fun i ↦ (w i : ℝ)) ≤
          qform N ((1 - P) *ᵥ (fun i ↦ (w i : ℝ))) := by
  let P := (output a B).proj
  let N := (matrixOf a.2.1 M).map (algebraMap ℚ ℝ)
  let θ : ℝ := greedyThreshold a.2.2.1 a.2.2.2.1
  let A := θ • (1 : Mat a.2.1) - (1 - P) * N * (1 - P)
  have hP : Projection P := (Geometry.basis_geometry a B hB).1
  have hN : Nᵀ = N := by simpa only [IsHermitian,
    conjTranspose_eq_transpose_of_trivial] using hM.1
  have hC := DetRoundAux.projection_compl P hP
  have hA : Aᵀ = A := by
    simp only [A, transpose_sub, transpose_smul, transpose_one, transpose_mul, hC.1, hN]
    rw [Matrix.mul_assoc]
  have hrep : ∀ i j : Fin a.2.1, A i j = SoS.PDTestRat.entry (pdTable a B M) i j := by
    intro i j
    exact congrArg (fun T ↦ T i j) (test_matrix a B M).symm
  obtain ⟨hnone, hsome⟩ := SoS.PDTestRat.test_spec (pdTable a B M)
    (by simp [pdTable, table]) A hrep hA
  have he (v : Vec a.2.1) : qform A v = θ * sqnorm v - qform N ((1 - P) *ᵥ v) := by
    rw [qform, show A = θ • 1 - (1 - P) * N * (1 - P) from rfl,
      sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul]
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← DetRoundAux.projection_dot (1 - P) hC]
    rfl
  refine ⟨?_, ?_⟩
  · intro hn v
    by_cases hv : v = 0
    · simp [hv, qform]
    · have h := hnone hn v hv
      change 0 < qform A v at h
      rw [he] at h
      change qform ((1 - P) * N * (1 - P)) v ≤ qform (θ • (1 : Mat a.2.1)) v
      simp only [qform, ← mulVec_mulVec, ← DetRoundAux.projection_dot (1 - P) hC,
        smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
      exact (sub_pos.1 h).le
  · intro y hy
    obtain ⟨w, hw, hw0, hwA⟩ := hsome y hy
    refine ⟨w, hw, hw0, ?_⟩
    change qform A (fun i ↦ (w i : ℝ)) ≤ 0 at hwA
    rw [he] at hwA
    linarith

theorem scalar_sqnorm {d : ℕ} (s : ℝ) (v : Vec d) :
    sqnorm (s • v) = s ^ 2 * sqnorm v := by
  simp only [sqnorm, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem scalar_qform {d : ℕ} (M : Mat d) (s : ℝ) (v : Vec d) :
    qform M (s • v) = s ^ 2 * qform M v := by
  simp only [qform, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem entry_sq_le {d : ℕ} (v : Vec d) (i : Fin d) : v i ^ 2 ≤ sqnorm v := by
  simpa only [sqnorm, dotProduct, ← pow_two] using
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i)

theorem rounding_vector {d p : ℕ} (l : Vector) (hl : l.length = d)
    (hu : sqnorm (fun i : Fin d ↦ (vectorOf d l i : ℝ)) < 1) :
    let v := l.map (roundRat p)
    v.length = d ∧ (∀ q ∈ v, -1 ≤ q ∧ q ≤ 1) ∧
      ∀ i : Fin d, |(vectorOf d v i : ℝ) - vectorOf d l i| ≤ 1 / (2 : ℝ) ^ p := by
  let u : Vec d := fun i ↦ (vectorOf d l i : ℝ)
  have hentry (i : Fin d) : |vectorOf d l i| < 1 := by
    have hs := (entry_sq_le u i).trans_lt hu
    have he : |u i| < 1 := by nlinarith [sq_abs (u i), abs_nonneg (u i)]
    have he' : |((vectorOf d l i : ℚ) : ℝ)| < 1 := he
    rw [← Rat.cast_abs, ← Rat.cast_one] at he'
    exact Rat.cast_lt.1 he'
  have hr (q : ℚ) (hq : q ∈ l) : -1 ≤ roundRat p q ∧ roundRat p q ≤ 1 := by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
    have he : vectorOf d l ⟨j, by omega⟩ = l[j] :=
      List.getD_eq_getElem _ _ hj
    have hq := abs_lt.1 (he ▸ hentry ⟨j, by omega⟩)
    refine ⟨?_, ?_⟩
    · unfold roundRat
      rw [le_div_iff₀ (by positivity)]
      have hf : -(2 : ℤ) ^ p ≤ ⌊(2 : ℚ) ^ p * l[j]⌋ := by
        apply Int.le_floor.2
        push_cast
        nlinarith [pow_pos (by norm_num : (0 : ℚ) < 2) p]
      have hc := Int.cast_le (R := ℚ) |>.2 hf
      push_cast at hc
      linarith
    · unfold roundRat
      rw [div_le_iff₀ (by positivity)]
      have hf := Int.floor_le ((2 : ℚ) ^ p * l[j])
      nlinarith [pow_pos (by norm_num : (0 : ℚ) < 2) p]
  refine ⟨by simp [hl], ?_, ?_⟩
  · intro q hq
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hq
    exact hr r hr'
  · intro i
    have he : vectorOf d (l.map (roundRat p)) i = roundRat p (vectorOf d l i) := by
      change (l.map (roundRat p)).getD i.val 0 = roundRat p (l.getD i.val 0)
      rw [SoS.PDTestRat.getD_map_of_eq _ _ _ (d' := 0) (by simp [roundRat])]
    rw [he]
    have h : 0 ≤ vectorOf d l i - roundRat p (vectorOf d l i) ∧
        vectorOf d l i - roundRat p (vectorOf d l i) < 1 / (2 : ℚ) ^ p := by
      unfold roundRat
      constructor
      · rw [sub_nonneg, div_le_iff₀ (by positivity)]
        simpa only [mul_comm] using Int.floor_le ((2 : ℚ) ^ p * vectorOf d l i)
      · rw [lt_div_iff₀ (by positivity)]
        have hf := Int.lt_floor_add_one ((2 : ℚ) ^ p * vectorOf d l i)
        have hp : (2 : ℚ) ^ p ≠ 0 := by positivity
        have he : (vectorOf d l i -
            (⌊(2 : ℚ) ^ p * vectorOf d l i⌋ : ℚ) / 2 ^ p) * 2 ^ p =
              2 ^ p * vectorOf d l i - (⌊(2 : ℚ) ^ p * vectorOf d l i⌋ : ℚ) := by
          field_simp
        rw [he]
        linarith
    have hh : |roundRat p (vectorOf d l i) - vectorOf d l i| ≤ 1 / (2 : ℚ) ^ p := by
      rw [abs_sub_comm, abs_of_nonneg h.1]
      exact h.2.le
    have hh' := Rat.cast_le (K := ℝ) |>.2 hh
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one,
      Rat.cast_pow, Rat.cast_ofNat] using hh'

theorem candidate_normalization (a : RoundArgs) (B : Points) (M : MatrixL) (y : List ℤ)
    (hB : GoodBasis a B) (hM : ((matrixOf a.2.1 M).map (algebraMap ℚ ℝ)).PosSemidef)
    (hy : SoS.PDTestRat.test (pdTable a B M) = some y) :
    ∃ l : Vector, l.length = a.2.1 ∧
      (1 / 4 ≤ sqnorm (fun i ↦ (vectorOf a.2.1 l i : ℝ)) ∧
        sqnorm (fun i ↦ (vectorOf a.2.1 l i : ℝ)) < 1) ∧
      (1 - (output a B).proj) *ᵥ (fun i ↦ (vectorOf a.2.1 l i : ℝ)) =
        (fun i ↦ (vectorOf a.2.1 l i : ℝ)) ∧
      (greedyThreshold a.2.2.1 a.2.2.2.1 : ℝ) / 4 ≤
        qform ((matrixOf a.2.1 M).map (algebraMap ℚ ℝ))
          (fun i ↦ (vectorOf a.2.1 l i : ℝ)) ∧
      candidate a B y = l.map (roundRat (greedyPrecision a)) := by
  let P := (output a B).proj
  let C := 1 - P
  let N := (matrixOf a.2.1 M).map (algebraMap ℚ ℝ)
  let θ : ℝ := greedyThreshold a.2.2.1 a.2.2.2.1
  have hP : Projection P := (Geometry.basis_geometry a B hB).1
  have hC : Projection C := DetRoundAux.projection_compl P hP
  have hθ : 0 < θ := (precision_error a).1
  obtain ⟨w, hw, hw0, henergy⟩ := (pd_spec a B M hB hM).2 y hy
  let x := mulVecL a.2.1 (complement a.2.1 B) (y.map fun z : ℤ ↦ (z : ℚ))
  let xr : Vec a.2.1 := fun i ↦ (vectorOf a.2.1 x i : ℝ)
  have hxlen : x.length = a.2.1 := by simp [x, mulVecL]
  have hx : xr = C *ᵥ (fun i ↦ (w i : ℝ)) := by
    have hr : RepV x (matrixOf a.2.1 (complement a.2.1 B) *ᵥ fun i ↦ (w i : ℚ)) := by
      apply mulVecL_rep (fun _ _ ↦ rfl)
      intro i
      simp [hw, List.map_ofFn, Function.comp_def]
    have hc := mulVec_cast (matrixOf a.2.1 (complement a.2.1 B)) (fun i ↦ (w i : ℚ))
    change ((matrixOf a.2.1 (complement a.2.1 B)).map (algebraMap ℚ ℝ) *ᵥ
      (fun i ↦ (w i : ℝ))) = _ at hc
    rw [Geometry.complement_eq] at hc
    funext i
    change (x.getD i.val 0 : ℝ) = _
    rw [hr i]
    exact congrFun hc.symm i
  have hwpos : 0 < sqnorm (fun i ↦ (w i : ℝ)) := by
    have hn := DetRoundAux.sqnorm_nonneg (fun i ↦ (w i : ℝ))
    by_contra! hz
    have he := dotProduct_self_eq_zero.1 (le_antisymm hz hn)
    apply hw0
    funext i
    have hi := congrFun he i
    change (w i : ℝ) = 0 at hi
    exact Int.cast_eq_zero.1 hi
  have hxpos : 0 < sqnorm xr := by
    by_contra! hz
    have he := dotProduct_self_eq_zero.1
      (le_antisymm hz (DetRoundAux.sqnorm_nonneg xr))
    rw [← hx, he] at henergy
    simp only [qform, mulVec_zero, dotProduct_zero] at henergy
    exact (mul_pos hθ hwpos).not_ge henergy
  have hxrat : 0 < dotL a.2.1 x x := by
    have he : (dotL a.2.1 x x : ℝ) = sqnorm xr := by
      rw [dotL_eq (fun _ ↦ rfl) (fun _ ↦ rfl), ← dotProduct_cast]
      rfl
    exact Rat.cast_pos.1 (he ▸ hxpos)
  let s := scaleL (dotL a.2.1 x x) / 2
  let l := x.map (s * ·)
  let u : Vec a.2.1 := fun i ↦ (vectorOf a.2.1 l i : ℝ)
  have hu : u = (s : ℝ) • xr := by
    funext i
    change ((x.map (s * ·)).getD i.val 0 : ℝ) = (s : ℝ) * _
    rw [SoS.PDTestRat.getD_map_of_eq _ _ _ (d' := 0) (by simp)]
    push_cast
    rfl
  have hs := scaleL_spec hxrat
  have hnorm : 1 / 4 ≤ sqnorm u ∧ sqnorm u < 1 := by
    have he : sqnorm u = ((s ^ 2 * dotL a.2.1 x x : ℚ) : ℝ) := by
      rw [hu, scalar_sqnorm, dotL_eq (fun _ ↦ rfl) (fun _ ↦ rfl),
        Rat.cast_mul, Rat.cast_pow, ← dotProduct_cast]
      rfl
    rw [he]
    have hs' : 1 / 4 ≤ s ^ 2 * dotL a.2.1 x x ∧ s ^ 2 * dotL a.2.1 x x < 1 := by
      dsimp only [s]
      constructor <;> nlinarith only [hs.1, hs.2]
    constructor
    · have h := Rat.cast_le (K := ℝ) |>.2 hs'.1
      norm_num at h ⊢
      exact h
    · have h := Rat.cast_lt (K := ℝ) |>.2 hs'.2
      norm_num at h ⊢
      exact h
  have hCu : C *ᵥ u = u := by rw [hu, hx, mulVec_smul, mulVec_mulVec, hC.2]
  have huenergy : θ / 4 ≤ qform N u := by
    have hc := DetRoundAux.projection_contract C hC (fun i ↦ (w i : ℝ))
    rw [← hx] at hc henergy
    have he : θ * sqnorm xr ≤ qform N xr :=
      (mul_le_mul_of_nonneg_left hc hθ.le).trans henergy
    have he' := mul_le_mul_of_nonneg_left he (sq_nonneg (s : ℝ))
    rw [hu, scalar_qform]
    have hn := hnorm.1
    rw [hu, scalar_sqnorm] at hn
    nlinarith
  have hl : l.length = a.2.1 := by simp [l, hxlen]
  refine ⟨l, hl, hnorm, hCu, huenergy, ?_⟩
  simp only [candidate, x, s, l, List.map_map, Function.comp_def]

theorem candidate_spec (a : RoundArgs) (B : Points) (M : MatrixL) (y : List ℤ)
    (hB : GoodBasis a B) (hM : ((matrixOf a.2.1 M).map (algebraMap ℚ ℝ)).PosSemidef)
    (ht : ((matrixOf a.2.1 M).map (algebraMap ℚ ℝ)).trace ≤ 5 / 4)
    (hy : SoS.PDTestRat.test (pdTable a B M) = some y) :
    acceptable a B (candidate a B y) ∧
      let P := (output a B).proj
      let z := (1 - P) *ᵥ (fun i ↦ (vectorOf a.2.1 (candidate a B y) i : ℝ))
      (greedyThreshold a.2.2.1 a.2.2.2.1 : ℝ) / 8 ≤
        qform ((matrixOf a.2.1 M).map (algebraMap ℚ ℝ)) z := by
  let P := (output a B).proj
  let C := 1 - P
  let N := (matrixOf a.2.1 M).map (algebraMap ℚ ℝ)
  let θ : ℝ := greedyThreshold a.2.2.1 a.2.2.2.1
  let δ : ℝ := 1 / (2 : ℝ) ^ greedyPrecision a
  have hP : Projection P := (Geometry.basis_geometry a B hB).1
  have hC : Projection C := DetRoundAux.projection_compl P hP
  have hθ : 0 < θ := (precision_error a).1
  obtain ⟨l, hl, hnorm, hCu, huenergy, hv⟩ := candidate_normalization a B M y hB hM hy
  let u : Vec a.2.1 := fun i ↦ (vectorOf a.2.1 l i : ℝ)
  change C *ᵥ u = u at hCu
  change 1 / 4 ≤ sqnorm u ∧ sqnorm u < 1 at hnorm
  change θ / 4 ≤ qform N u at huenergy
  obtain ⟨hvlen, hvbounds, hverr⟩ :=
    rounding_vector (p := greedyPrecision a) l hl hnorm.2
  let v : Vec a.2.1 := fun i ↦ (vectorOf a.2.1 (candidate a B y) i : ℝ)
  have hverr' : ∀ i, |v i - u i| ≤ δ := by
    intro i
    change |(vectorOf a.2.1 (candidate a B y) i : ℝ) - vectorOf a.2.1 l i| ≤ δ
    rw [hv]
    exact hverr i
  have hvabs : ∀ i, |v i| ≤ 1 := by
    intro i
    have hi : (candidate a B y).getD i.val 0 ∈ candidate a B y := by
      rw [List.getD_eq_getElem _ _ (by rw [hv, hvlen]; exact i.isLt)]
      exact List.getElem_mem _
    have he := hvbounds ((candidate a B y).getD i.val 0) (by rw [← hv]; exact hi)
    have he' : -1 ≤ vectorOf a.2.1 (candidate a B y) i ∧
        vectorOf a.2.1 (candidate a B y) i ≤ 1 := he
    have hh := Rat.cast_le (K := ℝ) |>.2 (abs_le.2 he')
    simpa only [Rat.cast_abs, Rat.cast_one] using hh
  have huabs : ∀ i, |u i| ≤ 1 := by
    intro i
    have hi := entry_sq_le u i
    nlinarith [sq_abs (u i), abs_nonneg (u i), hnorm.2]
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have herror : sqnorm (v - u) ≤ (a.2.1 * δ) ^ 2 := by
    calc
      _ = ∑ i, (v i - u i) ^ 2 := by simp only [sqnorm, dotProduct, Pi.sub_apply, pow_two]
      _ ≤ ∑ _i : Fin a.2.1, δ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hverr' i) 2
      _ ≤ _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hd : (a.2.1 : ℝ) ≤ (a.2.1 : ℝ) ^ 2 := by
          exact_mod_cast (show a.2.1 ≤ a.2.1 ^ 2 by nlinarith)
        nlinarith
  have herror' : Real.sqrt (sqnorm (v - u)) ≤ a.2.1 * δ :=
    (Real.sqrt_le_left (by positivity)).2 herror
  have hdδ : (a.2.1 : ℝ) * δ ≤ θ / 480 := by
    have h := (precision_error a).2
    have hh : (a.2.1 + 1 : ℝ) * δ ≤ θ / 480 := by
      simpa only [δ, div_eq_mul_inv, one_mul] using h
    nlinarith
  have hθ1 : θ ≤ 1 := by
    dsimp only [θ, greedyThreshold]
    push_cast
    exact (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hzerr : Real.sqrt (sqnorm (C *ᵥ v - u)) ≤ a.2.1 * δ := by
    rw [← hCu, ← mulVec_sub]
    exact (Real.sqrt_le_sqrt (DetRoundAux.projection_contract C hC _)).trans herror'
  have hzu : Real.sqrt (sqnorm (C *ᵥ v)) ≤ 9 / 8 := by
    have h := DRTrace.norm_sub_le (C *ᵥ v) u
    have hu' : Real.sqrt (sqnorm u) ≤ 1 := by
      exact (Real.sqrt_le_left (by norm_num)).2 (by simpa using hnorm.2.le)
    linarith
  have hzl : 3 / 8 ≤ Real.sqrt (sqnorm (C *ᵥ v)) := by
    have h := DRTrace.norm_sub_le u (C *ᵥ v)
    rw [DRTrace.sqnorm_sub_comm] at h
    have hu' : 1 / 2 ≤ Real.sqrt (sqnorm u) := by
      have hs := Real.sq_sqrt (DetRoundAux.sqnorm_nonneg u)
      nlinarith [Real.sqrt_nonneg (sqnorm u), hnorm.1]
    linarith
  have hzsq : 9 / 64 ≤ sqnorm (C *ᵥ v) ∧ sqnorm (C *ᵥ v) ≤ 81 / 64 := by
    have hs := Real.sq_sqrt (DetRoundAux.sqnorm_nonneg (C *ᵥ v))
    constructor <;> nlinarith [Real.sqrt_nonneg (sqnorm (C *ᵥ v))]
  have haccept : acceptable a B (candidate a B y) := by
    refine ⟨hv ▸ hvlen, hv ▸ hvbounds, ?_, ?_⟩
    · have he := hzsq.1
      rw [← Geometry.residual_eq] at he
      apply Rat.cast_le (K := ℝ) |>.1
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
      exact he
    · have he := hzsq.2
      rw [← Geometry.residual_eq] at he
      apply Rat.cast_le (K := ℝ) |>.1
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
      exact he
  refine ⟨haccept, ?_⟩
  have hCMC : (C * N * C).PosSemidef := by
    have h := hM.mul_mul_conjTranspose_same C
    simpa only [conjTranspose_eq_transpose_of_trivial, hC.1] using h
  have htrace : (C * N * C).trace ≤ 5 / 4 := by
    rw [trace_mul_cycle, hC.2]
    exact (DetRoundAux.trace_projection_le N C hM hC).trans ht
  have he := qform_round_error (C * N * C) hCMC v u δ hδ hvabs huabs hverr'
  have hq (x : Vec a.2.1) : qform (C * N * C) x = qform N (C *ᵥ x) := by
    rw [qform, ← mulVec_mulVec, ← mulVec_mulVec, ← DetRoundAux.projection_dot C hC]
    rfl
  rw [hq, hq, hCu] at he
  have htr0 : 0 ≤ (C * N * C).trace := hCMC.trace_nonneg
  have heb : 2 * δ * a.2.1 * (C * N * C).trace ≤ θ / 192 := by
    nlinarith [mul_le_mul_of_nonneg_left htrace
      (by positivity : 0 ≤ 2 * δ * a.2.1)]
  have hlower := (abs_le.1 he).1
  change θ / 8 ≤ qform N (C *ᵥ v)
  linarith

theorem greedyStep_prefix (a : RoundArgs) (fuel : ℕ) (M : MatrixL) (s : Bool × Points) :
    s.2 <+: (greedyStep a fuel M s).2 ∧
      (greedyStep a fuel M s).2.length ≤ s.2.length + 1 := by
  unfold greedyStep
  split
  · exact ⟨List.prefix_refl _, by omega⟩
  · split
    · exact ⟨List.prefix_refl _, by change s.2.length ≤ s.2.length + 1; omega⟩
    · dsimp only
      split
      · exact ⟨List.prefix_refl _, by change s.2.length ≤ s.2.length + 1; omega⟩
      · split
        · exact ⟨List.prefix_append _ _, by simp⟩
        · exact ⟨List.prefix_refl _, by change s.2.length ≤ s.2.length + 1; omega⟩

theorem greedy_iterate_prefix (a : RoundArgs) (fuel : ℕ) (M : MatrixL)
    (s : Bool × Points) (n : ℕ) :
    s.2 <+: (((greedyStep a fuel M)^[n]) s).2 ∧
      (((greedyStep a fuel M)^[n]) s).2.length ≤ s.2.length + n := by
  induction n with
  | zero => exact ⟨List.prefix_refl _, by simp⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := greedyStep_prefix a fuel M (((greedyStep a fuel M)^[n]) s)
    exact ⟨ih.1.trans h.1, by omega⟩

theorem append_fuel (I : RoundInput) (B : Points) (v : Vector)
    (hB : GoodBasis (roundArgs I) B) (hv : acceptable (roundArgs I) B v)
    (hg : OnGrid (roundArgs I) v) (hlen : B.length < rankCap I.radius I.rankBound) :
    (encPoints (B ++ [v])).length ≤ roundFuel I := by
  apply (Bounds.basis_size_bound (roundArgs I) (B ++ [v]) (.snoc hB hv hg) ?_).trans
    (Bounds.sufficient_basis_fuel I)
  simp only [List.length_append, List.length_singleton]
  exact Nat.succ_le_of_lt hlen

private theorem rayleigh_bound (θ q t : ℝ) (hθ : 0 < θ) (hq : θ / 8 ≤ q)
    (ht : 9 / 64 ≤ t ∧ t ≤ 81 / 64) : θ / 16 ≤ q / t := by
  rw [le_div_iff₀ (by linarith : 0 < t)]
  nlinarith

theorem append_trace_gain (a : RoundArgs) (B : Points) (v : Vector) (N : Mat a.2.1)
    (hB : GoodBasis a B) (hv : acceptable a B v) (hg : OnGrid a v)
    (he : (greedyThreshold a.2.2.1 a.2.2.2.1 : ℝ) / 8 ≤
      qform N ((1 - (output a B).proj) *ᵥ (fun i ↦ (vectorOf a.2.1 v i : ℝ)))) :
    ((output a B).proj * N).trace +
        (greedyThreshold a.2.2.1 a.2.2.2.1 : ℝ) / 16 ≤
      ((output a (B ++ [v])).proj * N).trace := by
  have hz : (9 / 64 : ℝ) ≤ sqnorm ((1 - (output a B).proj) *ᵥ
      (fun i ↦ (vectorOf a.2.1 v i : ℝ))) ∧
      sqnorm ((1 - (output a B).proj) *ᵥ (fun i ↦ (vectorOf a.2.1 v i : ℝ))) ≤
        81 / 64 := by
    rw [← Geometry.residual_eq]
    constructor
    · have h := Rat.cast_le (K := ℝ) |>.2 hv.2.2.1
      norm_num at h ⊢
      exact h
    · have h := Rat.cast_le (K := ℝ) |>.2 hv.2.2.2
      norm_num at h ⊢
      exact h
  rw [snoc_trace a B v N hB hv hg]
  exact add_le_add le_rfl (rayleigh_bound _ _ _ (precision_error a).1 he hz)

theorem greedy_step_progress (I : RoundInput) (B : Points) (M : MatrixL)
    (hB : GoodBasis (roundArgs I) B) (hlen : B.length < rankCap I.radius I.rankBound)
    (hM : ((matrixOf (roundArgs I).2.1 M).map (algebraMap ℚ ℝ)).PosSemidef)
    (ht : ((matrixOf (roundArgs I).2.1 M).map (algebraMap ℚ ℝ)).trace ≤ 5 / 4) :
    let s := greedyStep (roundArgs I) (roundFuel I) M (false, B)
    let N := (matrixOf (roundArgs I).2.1 M).map (algebraMap ℚ ℝ)
    let θ : ℝ := greedyThreshold I.radius I.rankBound
    (s.1 = true ∧ s.2 = B ∧ Common.LE
      ((1 - (output (roundArgs I) B).proj) * N * (1 - (output (roundArgs I) B).proj))
        (θ • (1 : Mat (roundArgs I).2.1))) ∨
      (s.1 = false ∧ ((output (roundArgs I) B).proj * N).trace + θ / 16 ≤
        ((output (roundArgs I) s.2).proj * N).trace) := by
  let a := roundArgs I
  let N := (matrixOf (roundArgs I).2.1 M).map (algebraMap ℚ ℝ)
  let θ : ℝ := greedyThreshold I.radius I.rankBound
  have hθ : 0 < θ := (precision_error a).1
  cases hy : SoS.PDTestRat.test (pdTable a B M) with
  | none =>
    have hc := (pd_spec a B M hB hM).1 hy
    left
    have hy' := hy
    unfold pdTable at hy'
    have hs : greedyStep a (roundFuel I) M (false, B) = (true, B) := by
      simp only [greedyStep, Bool.false_eq_true, ↓reduceIte,
        show ¬B.length ≥ rankCap a.2.2.1 a.2.2.2.1 from Nat.not_le.2 hlen, hy']
    exact ⟨congrArg Prod.fst hs, congrArg Prod.snd hs, hc⟩
  | some y =>
    obtain ⟨hv, he⟩ := candidate_spec a B M y hB hM ht hy
    have hg := candidate_grid a B y
    have hf := append_fuel I B (candidate a B y) hB hv hg hlen
    have hs : greedyStep a (roundFuel I) M (false, B) =
        (false, B ++ [candidate a B y]) := by
      simp only [greedyStep, Bool.false_eq_true, ↓reduceIte,
        show ¬B.length ≥ rankCap a.2.2.1 a.2.2.2.1 from by exact Nat.not_le.2 hlen]
      change (match SoS.PDTestRat.test (pdTable a B M) with
        | none => (true, B)
        | some y => if acceptable a B (candidate a B y) ∧
            (encPoints (B ++ [candidate a B y])).length ≤ roundFuel I
          then (false, B ++ [candidate a B y]) else (true, B)) = _
      simp only [hy, hv, hf, and_self, ite_true]
    right
    change (greedyStep a (roundFuel I) M (false, B)).1 = false ∧ _
    rw [hs]
    refine ⟨rfl, ?_⟩
    exact append_trace_gain a B (candidate a B y) N hB hv hg he

/-- Decode every state of the actual bounded greedy loop. -/
def captureTrace (I : RoundInput) (B : Points) (M : MatrixL) : DRCaptureTrace I.ambient :=
  ⟨fun t ↦ let s := ((greedyStep (roundArgs I) (roundFuel I) M)^[t]) (false, B)
    (s.1, output (roundArgs I) s.2)⟩

/-- Concrete PD tests and rational appends discharge the local abstract capture laws. -/
theorem captureTrace_spec (I : RoundInput) (B : Points) (M : MatrixL)
    (hB : Safe (roundArgs I) (roundFuel I) B)
    (hlen : B.length + greedyCap I.radius I.rankBound ≤ rankCap I.radius I.rankBound)
    (hM : ((matrixOf I.ambient M).map (algebraMap ℚ ℝ)).PosSemidef)
    (ht : ((matrixOf I.ambient M).map (algebraMap ℚ ℝ)).trace ≤ 5 / 4) :
    DRCaptureSpec I ((matrixOf I.ambient M).map (algebraMap ℚ ℝ))
      (output (roundArgs I) B) (captureTrace I B M) := by
  let a := roundArgs I
  let fuel := roundFuel I
  let state (t : ℕ) := ((greedyStep a fuel M)^[t]) (false, B)
  have hsafe (t : ℕ) : Safe a fuel (state t).2 :=
    iterate_preserves _ (fun s : Bool × Points ↦ Safe a fuel s.2)
      (greedyStep_safe a fuel M) (false, B) hB t
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro t
    exact (Geometry.basis_geometry a _ (hsafe t).2.2).1
  · intro t hb
    change (state t).1 = true at hb
    change ((state (t + 1)).1, output a (state (t + 1)).2) = _
    have he : state (t + 1) = state t := by
      dsimp only [state]
      rw [Function.iterate_succ_apply']
      change greedyStep a fuel M (state t) = state t
      simp only [greedyStep, hb, ↓reduceIte]
    rw [he]
    rfl
  · intro t htcap hb
    change (state t).1 = false at hb
    have hlength := (greedy_iterate_prefix a fuel M (false, B) t).2
    have hsmall : (state t).2.length < rankCap I.radius I.rankBound := by
      change (state t).2.length ≤ B.length + t at hlength
      omega
    have hh := greedy_step_progress I (state t).2 M (hsafe t).2.2 hsmall hM ht
    have he : (false, (state t).2) = state t := Prod.ext hb.symm rfl
    rw [he] at hh
    change _ ∨ _ at hh
    simp only [captureTrace, Function.iterate_succ_apply']
    rcases hh with ⟨hb', hD, hc⟩ | ⟨hb', hgain⟩
    · exact Or.inl ⟨hb', congrArg (output a) hD, hc⟩
    · exact Or.inr ⟨hb', hgain⟩


end

end ABBKS26.Assembly.Exec.RoundCertificates.Capture
