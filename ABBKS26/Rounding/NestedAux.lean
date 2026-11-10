module

public import ABBKS26.Rounding.Family
public import Background.SumOfSquares.GridMoments
public import Mathlib.Analysis.Matrix.PosDef

/-! Helpers for the bounded Gram encoding. -/

@[expose] public section

namespace ABBKS26.Rounding.NestedAux

noncomputable section

open MvPolynomial Matrix
open scoped BigOperators

private theorem factor {ι : Type*} [Fintype ι] {Q : Matrix ι ι ℝ}
    (hQ : Q.PosSemidef) : ∃ G : Matrix ι ι ℝ, G * Gᵀ = Q := by
  classical
  let U : Matrix ι ι ℝ := hQ.1.eigenvectorUnitary
  refine ⟨U * diagonal (fun i ↦ Real.sqrt (hQ.1.eigenvalues i)), ?_⟩
  have hD : diagonal (fun i ↦ Real.sqrt (hQ.1.eigenvalues i)) *
      diagonal (fun i ↦ Real.sqrt (hQ.1.eigenvalues i)) =
        diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id]
    exact Real.mul_self_sqrt (hQ.eigenvalues_nonneg i)
  conv_rhs => rw [hQ.1.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, transpose_mul, diagonal_transpose, ← mul_assoc,
    mul_assoc U, hD, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

private theorem sum_sq_quad {ι σ : Type*} [Fintype ι] (G : Matrix ι ι ℝ)
    (e : ι → MvPolynomial σ ℝ) :
    ∑ c, (∑ a, C (G a c) * e a) ^ 2 =
      ∑ a, ∑ b, C ((G * Gᵀ) a b) * (e a * e b) := by
  have hL : ∀ c, (∑ a, C (G a c) * e a) ^ 2 =
      ∑ a, ∑ b, C (G a c * G b c) * (e a * e b) := fun c ↦ by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by
      rw [C_mul]
      ring
  have hR : ∀ a b, C ((G * Gᵀ) a b) * (e a * e b) =
      ∑ c, C (G a c * G b c) * (e a * e b) := fun a b ↦ by
    rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
    rfl
  simp only [hL, hR]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm

/-- Compression of a sum of squares to the prescribed monomial list, with its grid bound. -/
theorem boundedGram {d e : ℕ} (L : List (Fin d →₀ ℕ)) (hL : L.Nodup)
    (hmem : ∀ μ, μ ∈ L ↔ μ.degree ≤ e) (p : Common.RPoly d) (hp : IsSumSq p)
    (hd : p.totalDegree ≤ 2 * e) :
    ∃ G : Matrix (Fin L.length) (Fin L.length) ℝ,
      p = ∑ c, (∑ a, C (G a c) * monomial L[a] 1) ^ 2 ∧
      (∑ a, ∑ c, G a c ^ 2) ≤
        ((d + 1 : ℝ) ^ e * (SoS.interpBound e : ℝ) ^ (2 * d) * (e + 1 : ℝ) ^ d) *
          ∑ x : Fin d → Fin (e + 1), eval (SoS.gridPoint x) p := by
  classical
  obtain ⟨H, hH, hHd⟩ := SoS.IsSumSq.exists_list_of_totalDegree_le hp hd
  have hdeg : ∀ q ∈ H, q.totalDegree ≤ e := fun q hq ↦ by
    have := hHd q hq
    omega
  have reconstruct : ∀ q ∈ H,
      ∑ a : Fin L.length, C (q.coeff L[a]) * monomial L[a] 1 = q := by
    intro q hq
    simp only [C_mul_monomial, mul_one]
    simp only [Fin.getElem_fin]
    rw [Fin.sum_univ_fun_getElem L (fun μ ↦ monomial μ (q.coeff μ)),
      ← List.sum_toFinset _ hL]
    conv_rhs => rw [q.as_sum]
    symm
    apply Finset.sum_subset
    · intro μ hμ
      exact List.mem_toFinset.2 ((hmem μ).2 ((le_totalDegree hμ).trans (hdeg q hq)))
    · intro μ _ hμ
      simp [notMem_support_iff.1 hμ]
  let u : Fin H.length → Fin L.length → ℝ := fun k a ↦ H[k].coeff L[a]
  let Q : Matrix (Fin L.length) (Fin L.length) ℝ := ∑ k, vecMulVec (u k) (u k)
  have hQ : Q.PosSemidef := posSemidef_sum _ fun k _ ↦ by
    simpa using posSemidef_vecMulVec_self_star (u k)
  obtain ⟨G, hG⟩ := factor hQ
  have hcoeff : ∀ q : Common.RPoly d,
      ∑ a : Fin L.length, q.coeff L[a] ^ 2 ≤ SoS.coeffNorm q ^ 2 := by
    intro q
    simp only [Fin.getElem_fin]
    rw [Fin.sum_univ_fun_getElem L (fun μ ↦ q.coeff μ ^ 2),
      ← List.sum_toFinset _ hL,
      SoS.coeffNorm_eq_of_support_subset
        (Finset.subset_union_right (s₁ := L.toFinset)),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      fun _ _ _ ↦ sq_nonneg _
  refine ⟨G, ?_, ?_⟩
  · rw [sum_sq_quad, hG]
    simp only [Q, Matrix.sum_apply, vecMulVec_apply, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_rhs => arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    have hquad : ∀ k, (∑ a, ∑ b, C (u k a * u k b) *
        (monomial L[a] 1 * monomial L[b] 1)) = H[k] * H[k] := by
      intro k
      rw [← reconstruct H[k] (List.getElem_mem k.isLt)]
      simp only [Finset.sum_mul_sum, C_mul, u]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    conv_rhs => arg 2; ext k; rw [Finset.sum_comm, hquad]
    simpa only [Fin.getElem_fin, Fin.sum_univ_fun_getElem H (fun q ↦ q * q)] using hH
  · have htr : (∑ a, ∑ c, G a c ^ 2) = ∑ k, ∑ a, u k a ^ 2 := by
      have he : ∀ a, ∑ c, G a c ^ 2 = (G * Gᵀ) a a := fun a ↦ by
        simp [Matrix.mul_apply, sq]
      simp only [he, hG, Q, Matrix.sum_apply, vecMulVec_apply, ← sq]
      exact Finset.sum_comm
    rw [htr]
    calc
      _ ≤ ∑ k : Fin H.length, SoS.coeffNorm H[k] ^ 2 :=
        Finset.sum_le_sum fun k _ ↦ hcoeff H[k]
      _ = (H.map fun q ↦ SoS.coeffNorm q ^ 2).sum :=
        by simpa only [Fin.getElem_fin] using
          Fin.sum_univ_fun_getElem H (fun q ↦ SoS.coeffNorm q ^ 2)
      _ ≤ _ := by
        have he : ∀ K : List (Common.RPoly d),
            (∀ q ∈ K, q.totalDegree ≤ e) →
            (K.map fun q ↦ SoS.coeffNorm q ^ 2).sum ≤
              ((d + 1 : ℝ) ^ e * (SoS.interpBound e : ℝ) ^ (2 * d) * (e + 1 : ℝ) ^ d) *
                ∑ x : Fin d → Fin (e + 1),
                  eval (SoS.gridPoint x) (K.map fun q ↦ q * q).sum := by
          intro K
          induction K with
          | nil => simp
          | cons q K ih =>
            intro hK
            simp only [List.map_cons, List.sum_cons, map_add, Finset.sum_add_distrib,
              mul_add]
            refine add_le_add ?_ (ih fun q hq ↦ hK q (List.mem_cons_of_mem _ hq))
            simpa only [map_mul, pow_two, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow,
              Nat.cast_add, Nat.cast_one] using
                SoS.coeffNorm_sq_le_sum_grid (hK q List.mem_cons_self)
        rw [hH]
        exact he H hdeg


/-- Concatenate finitely many blocks. -/
def pack (f : ℕ → List ℝ) (n : ℕ) : List ℝ := (List.range n).flatMap f

theorem pack_length (f : ℕ → List ℝ) (n : ℕ) :
    (pack f n).length = ((List.range n).map fun i ↦ (f i).length).sum := by
  simp [pack, List.length_flatMap]

theorem pack_get (f : ℕ → List ℝ) {n j k : ℕ} (hj : j < n) (hk : k < (f j).length) :
    (pack f n).getD (((List.range j).map fun i ↦ (f i).length).sum + k) 0 =
      (f j).getD k 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [pack, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change (pack f n ++ f n).getD _ 0 = _
    by_cases h : j < n
    · have hb : ((List.range j).map fun i ↦ (f i).length).sum + k < (pack f n).length := by
        rw [pack_length]
        have hh : ∀ m, j < m →
            ((List.range j).map fun i ↦ (f i).length).sum + (f j).length ≤
              ((List.range m).map fun i ↦ (f i).length).sum := by
          intro m
          induction m with
          | zero => omega
          | succ m ihm =>
            intro hm
            rw [List.range_succ, List.map_append, List.sum_append]
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
            by_cases hjm : j < m
            · exact (ihm hjm).trans (Nat.le_add_right _ _)
            · have : j = m := by omega
              subst j
              rfl
        have := hh n h
        omega
      rw [List.getD_append _ _ _ _ hb]
      exact ih h
    · have he : j = n := by omega
      subst j
      rw [← pack_length, List.getD_append_right _ _ _ _ (by omega),
        Nat.add_sub_cancel_left]

theorem pack_sq (f : ℕ → List ℝ) (n : ℕ) :
    ((pack f n).map fun x ↦ x ^ 2).sum =
      ((List.range n).map fun i ↦ ((f i).map fun x ↦ x ^ 2).sum).sum := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    simpa only [pack, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
        congrArg (fun x ↦ x + ((f n).map fun x ↦ x ^ 2).sum) ih

theorem pack_sq_le (f : ℕ → List ℝ) (n : ℕ) (b : ℝ)
    (h : ∀ j < n, ((f j).map fun x ↦ x ^ 2).sum ≤ b) :
    ((pack f n).map fun x ↦ x ^ 2).sum ≤ n * b := by
  rw [pack_sq]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have := ih (fun j hj ↦ h j (by omega))
    have := h n (by omega)
    push_cast
    linarith

theorem pack_index_lt (f : ℕ → List ℝ) {n j k : ℕ}
    (hj : j < n) (hk : k < (f j).length) :
    ((List.range j).map fun i ↦ (f i).length).sum + k < (pack f n).length := by
  induction n with
  | zero => omega
  | succ n ih =>
    have he : (pack f (n + 1)).length = (pack f n).length + (f n).length := by
      simp [pack, List.range_succ]
    rw [he]
    by_cases h : j < n
    · have := ih h
      omega
    · have : j = n := by omega
      subst j
      rw [← pack_length]
      omega

theorem pack_get_inside (f : ℕ → List ℝ) (pre post : List ℝ) {n j k : ℕ}
    (hj : j < n) (hk : k < (f j).length) :
    (pre ++ (pack f n ++ post)).getD
      (pre.length + ((List.range j).map fun i ↦ (f i).length).sum + k) 0 =
        (f j).getD k 0 := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  rw [show pre.length + ((List.range j).map fun i ↦ (f i).length).sum + k -
    pre.length = ((List.range j).map fun i ↦ (f i).length).sum + k by omega]
  rw [List.getD_append _ _ _ _ (pack_index_lt f hj hk), pack_get f hj hk]

theorem sum_getD_sq (L : List ℝ) :
    ∑ i ∈ Finset.range L.length, L.getD i 0 ^ 2 = (L.map fun x ↦ x ^ 2).sum := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : Fin L.length, L[i.val] ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [List.getD_eq_getElem _ _ i.isLt]
    _ = _ := Fin.sum_univ_fun_getElem L (fun x ↦ x ^ 2)

/-- Row-major matrix data. -/
def matrixData {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℝ) : List ℝ :=
  List.ofFn fun k : Fin (m * n) ↦ G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

@[simp] theorem matrixData_length {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℝ) :
    (matrixData G).length = m * n := by simp [matrixData]

theorem matrixData_get {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (j : Fin n) : (matrixData G).getD (i * n + j) 0 = G i j := by
  have hk : i * n + j < m * n := by
    calc
      _ < i * n + n := Nat.add_lt_add_left j.isLt _
      _ = (i + 1) * n := by ring
      _ ≤ m * n := Nat.mul_le_mul_right n i.isLt
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp only [matrixData, List.getElem_ofFn]
  have he : (⟨i * n + j, hk⟩ : Fin (m * n)) = finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [he]
  change G (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = _
  simp

theorem matrixData_sq {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℝ) :
    ((matrixData G).map fun x ↦ x ^ 2).sum = ∑ i, ∑ j, G i j ^ 2 := by
  rw [matrixData, List.map_ofFn, List.sum_ofFn]
  exact (Equiv.sum_comp finProdFinEquiv.symm (fun k ↦ G k.1 k.2 ^ 2)).trans
    (Fintype.sum_prod_type _)

/-- A sum of squares uses the even part of its degree budget. -/
theorem sos_budget {d b : ℕ} {p : Common.RPoly d} (hp : IsSumSq p)
    (hd : p.totalDegree ≤ b) : p.totalDegree ≤ 2 * (b / 2) := by
  obtain ⟨L, rfl, hL⟩ := SoS.IsSumSq.exists_list_of_totalDegree_le hp hd
  have hs : ∀ K : List (Common.RPoly d),
      (∀ q ∈ K, q.totalDegree ≤ 2 * (b / 2)) → K.sum.totalDegree ≤ 2 * (b / 2) := by
    intro K
    induction K with
    | nil => simp
    | cons q K ih =>
      intro hh
      exact (totalDegree_add _ _).trans (max_le (hh q List.mem_cons_self)
        (ih fun q hq ↦ hh q (List.mem_cons_of_mem _ hq)))
  apply hs
  intro q hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
  have := hL r hr
  exact (totalDegree_mul _ _).trans (by omega)

/-- Substitution preserves linear certificates and gives an explicit norm bound. -/
theorem aevalNq {σ τ : Type*} {A : SoS.System σ ℝ} {k e : ℕ} {M β : ℝ}
    {g : MvPolynomial σ ℝ} (h : SoS.DerivesNq A k M 1 g)
    (φ : σ → MvPolynomial τ ℝ) (hd : ∀ i, (φ i).totalDegree ≤ e)
    (hβ : 1 ≤ β) (hn : ∀ i, SoS.coeffNorm1 (φ i) ≤ β) :
    SoS.DerivesNq (A.map (aeval φ)) (k * e) (M * β ^ k) 1 (aeval φ g) := by
  classical
  have hM := h.nonneg
  obtain ⟨P, hP, hq⟩ := h
  refine ⟨P.subst φ hd, ?_, ?_⟩
  · intro S
    change SoS.coeffNorm1 (aeval φ (P.mult _)) ≤ _
    by_cases hz : P.mult
        (S.map (finCongr (List.length_map (aeval φ))).toEmbedding) = 0
    · simpa [hz] using mul_nonneg hM (pow_nonneg (by linarith) k)
    · have hdeg := P.degree_le _ hz
      exact (SoS.coeffNorm1_aeval_le φ hβ hn _).trans
        (mul_le_mul (hP _) (pow_le_pow_right₀ hβ (by omega))
          (pow_nonneg (by linarith) _) hM)
  · intro S hS
    change aeval φ (P.mult _) = 0
    rw [hq _ (by simpa using hS), map_zero]

/-- Multiplying a paired equality by an arbitrary polynomial keeps the proof linear. -/
theorem mul_eq {σ : Type*} {A : SoS.System σ ℝ} {f : MvPolynomial σ ℝ}
    (hf : f ∈ A) (hnf : -f ∈ A) (r : MvPolynomial σ ℝ) :
    SoS.DerivesNq A (2 * r.totalDegree + f.totalDegree)
      ((SoS.coeffNorm1 r + 1) ^ 2) 1 (r * f) := by
  let a := C (1 / 2 : ℝ) * (r + 1)
  let b := C (1 / 2 : ℝ) * (r - 1)
  have hd : ∀ s : MvPolynomial σ ℝ, s.totalDegree ≤ r.totalDegree →
      (s ^ 2).totalDegree ≤ 2 * r.totalDegree := fun s hs ↦
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hs)
  have ha : a.totalDegree ≤ r.totalDegree :=
    (totalDegree_mul _ _).trans (by
      rw [totalDegree_C, zero_add]
      exact (totalDegree_add _ _).trans (max_le le_rfl (by simp)))
  have hb : b.totalDegree ≤ r.totalDegree :=
    (totalDegree_mul _ _).trans (by
      rw [totalDegree_C, zero_add]
      exact (totalDegree_sub _ _).trans (max_le le_rfl (by simp)))
  have hna : SoS.coeffNorm1 (a ^ 2) ≤ (SoS.coeffNorm1 r + 1) ^ 2 / 2 := by
    have hnorm : SoS.coeffNorm1 a ≤ (SoS.coeffNorm1 r + 1) / 2 := by
      dsimp [a]
      rw [SoS.coeffNorm1_C_mul]
      have := SoS.coeffNorm1_add_le r 1
      rw [SoS.coeffNorm1_one] at this
      norm_num
      linarith
    have := SoS.coeffNorm1_pow_le a 2
    nlinarith [SoS.coeffNorm1_nonneg a, SoS.coeffNorm1_nonneg r]
  have hnb : SoS.coeffNorm1 (b ^ 2) ≤ (SoS.coeffNorm1 r + 1) ^ 2 / 2 := by
    have hnorm : SoS.coeffNorm1 b ≤ (SoS.coeffNorm1 r + 1) / 2 := by
      dsimp [b]
      rw [SoS.coeffNorm1_C_mul]
      have := SoS.coeffNorm1_sub_le r 1
      rw [SoS.coeffNorm1_one] at this
      norm_num
      linarith
    have := SoS.coeffNorm1_pow_le b 2
    nlinarith [SoS.coeffNorm1_nonneg b, SoS.coeffNorm1_nonneg r]
  have h₁ : SoS.DerivesNq A f.totalDegree 1 1 f :=
    SoS.DerivesNq.of_mem hf le_rfl le_rfl
  have h₂ : SoS.DerivesNq A f.totalDegree 1 1 (-f) :=
    SoS.DerivesNq.of_mem hnf (by rw [totalDegree_neg]) le_rfl
  have h₁ := h₁.mulSOS (SoS.IsSOS.sq a)
  have h₂ := h₂.mulSOS (SoS.IsSOS.sq b)
  have hsum := (h₁.mono (Nat.add_le_add_right (hd a ha) _) (by simpa using hna)).add
    (h₂.mono (Nat.add_le_add_right (hd b hb) _) (by simpa using hnb))
  have hc : (C (1 / 2 : ℝ) * C (1 / 2) * 4 : MvPolynomial σ ℝ) = 1 := by
    rw [show (4 : MvPolynomial σ ℝ) = C 4 from (map_ofNat C 4).symm,
      ← C_mul, ← C_mul]
    norm_num
  convert hsum.congr (show a ^ 2 * f + b ^ 2 * -f = r * f by
    dsimp [a, b]
    linear_combination (r * f) * hc) using 1
  ring

/-- Degree in the coefficient variables of an iterated polynomial. -/
def CoeffDegree {σ τ : Type*} (p : MvPolynomial σ (MvPolynomial τ ℝ)) (n : ℕ) : Prop :=
  ∀ μ, (p.coeff μ).totalDegree ≤ n

namespace CoeffDegree

variable {σ τ : Type*} {p q : MvPolynomial σ (MvPolynomial τ ℝ)} {m n : ℕ}

theorem mono (h : CoeffDegree p m) (hm : m ≤ n) : CoeffDegree p n :=
  fun μ ↦ (h μ).trans hm

theorem monomial (μ : σ →₀ ℕ) (c : MvPolynomial τ ℝ) :
    CoeffDegree (MvPolynomial.monomial μ c) c.totalDegree := by
  classical
  intro ν
  rw [coeff_monomial]
  split_ifs <;> simp

theorem const (c : MvPolynomial τ ℝ) : CoeffDegree (C c : MvPolynomial σ _) c.totalDegree :=
  monomial 0 c

theorem add (hp : CoeffDegree p n) (hq : CoeffDegree q n) : CoeffDegree (p + q) n := by
  intro μ
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact (totalDegree_add _ _).trans (max_le (hp μ) (hq μ))

theorem sub (hp : CoeffDegree p n) (hq : CoeffDegree q n) : CoeffDegree (p - q) n := by
  intro μ
  rw [coeff_sub]
  exact (totalDegree_sub _ _).trans (max_le (hp μ) (hq μ))

theorem mul (hp : CoeffDegree p m) (hq : CoeffDegree q n) : CoeffDegree (p * q) (m + n) := by
  classical
  intro μ
  rw [coeff_mul]
  apply totalDegree_finsetSum_le
  intro x _
  exact (totalDegree_mul _ _).trans (Nat.add_le_add (hp x.1) (hq x.2))

theorem sum {ι : Type*} (S : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial τ ℝ))
    (h : ∀ i ∈ S, CoeffDegree (f i) n) : CoeffDegree (∑ i ∈ S, f i) n := by
  classical
  intro μ
  rw [coeff_sum]
  exact totalDegree_finsetSum_le fun i hi ↦ h i hi μ

theorem pow (hp : CoeffDegree p n) (k : ℕ) : CoeffDegree (p ^ k) (k * n) := by
  induction k with
  | zero => simpa using (const (σ := σ) (1 : MvPolynomial τ ℝ))
  | succ k ih => simpa [pow_succ, Nat.succ_mul] using ih.mul hp

theorem prod {ι : Type*} (S : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial τ ℝ))
    (b : ι → ℕ) (h : ∀ i ∈ S, CoeffDegree (f i) (b i)) :
    CoeffDegree (∏ i ∈ S, f i) (∑ i ∈ S, b i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (const (σ := σ) (1 : MvPolynomial τ ℝ))
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

theorem eval_map {κ : Type*} (φ : κ → MvPolynomial σ (MvPolynomial τ ℝ))
    (hφ : ∀ i, CoeffDegree (φ i) n) (f : MvPolynomial κ ℝ) :
    CoeffDegree (aeval φ (f.map (C : ℝ →+* MvPolynomial τ ℝ))) (f.totalDegree * n) := by
  classical
  conv_lhs => rw [f.as_sum, map_sum, map_sum]
  apply sum
  intro μ hμ
  simp only [map_monomial, aeval_monomial, algebraMap_eq]
  have hc : CoeffDegree (C (C (f.coeff μ) : MvPolynomial τ ℝ) :
        MvPolynomial σ (MvPolynomial τ ℝ)) 0 := by
    simpa using const (σ := σ) (C (f.coeff μ) : MvPolynomial τ ℝ)
  have hp : CoeffDegree (μ.prod fun i k ↦ φ i ^ k) (μ.degree * n) := by
    unfold Finsupp.prod
    convert prod μ.support (fun i ↦ φ i ^ μ i) (fun i ↦ μ i * n)
      (fun i _ ↦ (hφ i).pow (μ i)) using 1
    rw [← Finset.sum_mul]
    rfl
  exact (hc.mul hp).mono (by
    simp only [zero_add]
    exact Nat.mul_le_mul_right n (le_totalDegree hμ))

end CoeffDegree

end
end ABBKS26.Rounding.NestedAux
