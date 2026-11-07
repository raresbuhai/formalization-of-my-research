module

public import BGHKLMM26.Exact
public import Background.PhiSeries

/-!
# The accuracy of the algorithm

On the event that the Gaussians `g` read from the coins lie in `[-R, R]`, the algorithm's
quantities are close to the ideal ones for the vectors `v = BGHKLMM26.Alg.vAlg`:

* `|ĝₖ - gₖ| ≤ 2/2^p` (`BGHKLMM26.Alg.abs_gHat_sub_le`), by the cells and bisection;
* `|ξ̂ₖ - ⟨vₖ, g⟩| ≤ E (1 + C)^k` (`BGHKLMM26.Alg.abs_xiHat_sub_le`) with
  `E = (R + 4)/2^p` and `C = n + 2/τ`, which bounds `∑_{l<k} |cₖₗ|`
  (`BGHKLMM26.Factor.sosVec_coef`);
* the shifted arguments `ξ̂ᵢ + λ f̂ᵢ` within `2^-(Z+Q₀)²` of `⟨vᵢ, g⟩ + λ fᵢ(g)`
  (`BGHKLMM26.Alg.abs_argL_sub_le`).
-/

@[expose] public section

namespace BGHKLMM26.Alg

open Real Factor Num SoS.Loop Gaussian Finset GW
open scoped RealInnerProductSpace

/-! ### Sizes -/

theorem length_frame (w : List Bool) : (Encoding.frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => simp [Encoding.frame]
  | cons b w ih =>
    simp only [Encoding.frame, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem length_le_flatMap_frame {α : Type} (f : α → List Bool) (l : List α) :
    l.length ≤ (l.flatMap fun a ↦ Encoding.frame (f a)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, length_frame]
    omega

/-- The size `Z` bounds the number of variables and of constraints. -/
theorem size_ge (I : Instance) : I.1 + I.2.length + 3 ≤ zPar I := le_rfl

/-- The size `Z` is at most the length of the encoded instance plus `2`. -/
theorem zPar_le_length (I : Instance) : zPar I ≤ (encInstance I).length + 2 := by
  unfold zPar
  have h : (encInstance I).length = (Encoding.frame (List.replicate I.1 true)).length +
      (I.2.flatMap fun c ↦ Encoding.frame (Encoding.encPair
        (Encoding.encPair Encoding.encNat Encoding.encNat)
        (Encoding.encPair Encoding.encBool Encoding.encRat) c)).length := by
    rw [← List.length_append]; rfl
  rw [h, length_frame, List.length_replicate]
  have := length_le_flatMap_frame (fun c ↦ Encoding.encPair
    (Encoding.encPair Encoding.encNat Encoding.encNat)
    (Encoding.encPair Encoding.encBool Encoding.encRat) c) I.2
  omega

theorem n_lt_zPar (I : Instance) : I.1 < zPar I := by have := size_ge I; omega

theorem three_le_zPar (I : Instance) : 3 ≤ zPar I := by have := size_ge I; omega

theorem degree_le_length (I : Instance) (v : ℕ) : degree I v ≤ I.2.length :=
  List.length_filter_le _ _

theorem foldr_max_le_nat {l : List ℕ} {b : ℕ} (h : ∀ x ∈ l, x ≤ b) : l.foldr max 0 ≤ b := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a List.mem_cons_self) (ih fun x hx ↦ h x (List.mem_cons_of_mem a hx))

theorem le_foldr_max_nat {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem maxDeg_le (I : Instance) : maxDeg I ≤ I.2.length :=
  foldr_max_le_nat fun x hx ↦ by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
    exact degree_le_length I v

theorem dPar_le (I : Instance) : dPar I ≤ zPar I := by
  have := size_ge I
  have := maxDeg_le I
  unfold dPar
  omega

theorem two_le_dPar (I : Instance) : 2 ≤ dPar I := le_max_left _ _

/-- The variables have degree at most `D`. -/
theorem maxDegreeLE_dPar {I : Instance} (hI : Valid I) : MaxDegreeLE I (dPar I) := by
  intro v
  by_cases hv : v < I.1
  · exact (le_foldr_max_nat (List.mem_map.2 ⟨v, List.mem_range.2 hv, rfl⟩)).trans
      (le_max_right _ _)
  · have : degree I v = 0 := by
      unfold degree
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc
      obtain ⟨hij, hj, -⟩ := hI.1 c hc
      simp only [decide_eq_true_eq, not_or]
      omega
    omega

theorem one_le_lPar (I : Instance) : 1 ≤ lPar I :=
  Nat.clog_pos (by norm_num) (by have := two_le_dPar I; omega)

theorem dPar_le_pow (I : Instance) : dPar I ≤ 2 ^ lPar I := Nat.le_pow_clog (by norm_num) _

theorem lPar_le (I : Instance) : lPar I ≤ dPar I :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem lPar_le_zPar (I : Instance) : lPar I ≤ zPar I := (lPar_le I).trans (dPar_le I)

theorem kPar_sq_gt (I : Instance) : 16 * lPar I + 4 < kPar I ^ 2 := by
  have := Nat.lt_succ_sqrt (16 * lPar I + 4)
  unfold kPar
  rw [sq]
  exact this

theorem kPar_sq_le (I : Instance) : kPar I ^ 2 ≤ 42 * lPar I := by
  have h1 := Nat.sqrt_le' (16 * lPar I + 4)
  have h2 := one_le_lPar I
  unfold kPar
  nlinarith [Nat.sqrt_le_self (16 * lPar I + 4)]

theorem five_le_kPar (I : Instance) : 5 ≤ kPar I := by
  have h := kPar_sq_gt I
  have h2 := one_le_lPar I
  by_contra hk
  push Not at hk
  have : kPar I ^ 2 ≤ 16 := by
    have : kPar I ≤ 4 := by omega
    nlinarith
  omega

theorem kPar_le (I : Instance) : kPar I ≤ 16 * lPar I + 5 := by
  have := Nat.sqrt_le_self (16 * lPar I + 4)
  unfold kPar
  omega

/-! ### Recovering the Gaussians -/

section Gaussians

variable (Q₀ : ℕ) (I : Instance)

/-- The cells of the coordinates of `g`, as the algorithm reads them. -/
noncomputable def cellsE (g : EuclideanSpace ℝ (Fin I.1)) (k : ℕ) : ℕ :=
  if h : k < I.1 then cellOf (tPar Q₀ I) (g ⟨k, h⟩) else 0

theorem one_le_rPar : 1 ≤ rPar Q₀ I := by
  unfold rPar
  have := three_le_zPar I
  have : 1 ≤ 2 ^ Q₀ := Nat.one_le_two_pow
  nlinarith

theorem two_le_rPar : 2 ≤ rPar Q₀ I := by
  unfold rPar
  have := three_le_zPar I
  have : 1 ≤ 2 ^ Q₀ := Nat.one_le_two_pow
  nlinarith

theorem natCast_add_one_le_two_pow (m : ℕ) : (m : ℝ) + 1 ≤ 2 ^ m := by
  exact_mod_cast Nat.lt_two_pow_self

variable {Q₀ I}

/-- **Recovering a Gaussian**: for `|gₖ| ≤ R`, `|ĝₖ - gₖ| ≤ 2/2^p`. -/
theorem abs_gHat_sub_le (g : EuclideanSpace ℝ (Fin I.1)) {k : ℕ} (hk : k < I.1)
    (hg : |g ⟨k, hk⟩| ≤ rPar Q₀ I) :
    |(gHat Q₀ I (cellsE Q₀ I g) k : ℝ) - g ⟨k, hk⟩| ≤ 2 / 2 ^ pPar Q₀ I := by
  set R := rPar Q₀ I
  set p := pPar Q₀ I
  set T := tPar Q₀ I
  set N := nSer Q₀ I
  set M := 30000 * (R + 1) ^ 4 with hM
  have hT : (2 : ℝ) ^ T = 2 ^ ((R + 1) ^ 2) * 2 ^ p * 256 := by
    rw [show T = (R + 1) ^ 2 + p + 8 from rfl, pow_add, pow_add]; norm_num
  have hN : (2 : ℝ) ^ N = 2 ^ M * 2 ^ T := by
    rw [show N = M + T from rfl, pow_add]
  have hR : (R : ℝ) + 1 ≤ 2 ^ M := by
    refine le_trans ?_ (natCast_add_one_le_two_pow M)
    have h1 : R + 1 ≤ (R + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
    have : R ≤ M := by rw [hM]; omega
    exact_mod_cast Nat.add_le_add_right this 1
  have h2T : (0 : ℝ) < 2 ^ T := by positivity
  have hB : 1 / 2 ^ (T + 1) + (((R : ℝ) + 1) / 2 ^ N + 2 / 2 ^ T) ≤
      1 / 2 ^ p * ((1 / 4) * (1 / 2) ^ ((R + 1) ^ 2)) := by
    have e1 : (1 : ℝ) / 2 ^ (T + 1) = 1 / 2 / 2 ^ T := by rw [pow_succ]; field_simp
    have e2 : ((R : ℝ) + 1) / 2 ^ N ≤ 1 / 2 ^ T := by
      rw [hN, div_le_div_iff₀ (by positivity) h2T]
      generalize (2 : ℝ) ^ M = A at hR
      calc ((R : ℝ) + 1) * 2 ^ T ≤ A * 2 ^ T := mul_le_mul_of_nonneg_right hR h2T.le
        _ = 1 * (A * 2 ^ T) := (one_mul _).symm
    have e3 : 1 / 2 ^ p * ((1 / 4) * (1 / 2 : ℝ) ^ ((R + 1) ^ 2)) = 64 / 2 ^ T := by
      rw [hT, one_div_pow]; field_simp; norm_num
    rw [e1, e3]
    have : (1 : ℝ) / 2 / 2 ^ T + 1 / 2 ^ T + 2 / 2 ^ T ≤ 64 / 2 ^ T := by
      rw [← add_div, ← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) h2T.le
    linarith
  have hn : 5 ≤ T := by simp only [T, tPar]; omega
  have hNR : 3 * ((R : ℝ) + 1) ^ 2 ≤ N := by
    have : 3 * (R + 1) ^ 2 ≤ N := by
      rw [show N = M + T from rfl, hM]
      have : (R + 1) ^ 2 ≤ (R + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega
    exact_mod_cast this
  have h := abs_cellInv_sub_le (n := T) (N := N) (K := kBis Q₀ I) (B := T) (R := R)
    (δ := 1 / 2 ^ p) hn hg hNR (by positivity) hB
  rw [gHat, cellsE, dite_eq_left hk]
  refine h.trans ?_
  -- `2 (R + 1) / 2^K ≤ 1/2^p` for `K = p + R + 2`.
  have hK : (2 : ℝ) ^ kBis Q₀ I = 2 ^ p * 2 ^ R * 4 := by
    rw [show kBis Q₀ I = p + R + 2 from rfl, pow_add, pow_add]; norm_num
  have hR2 : (R : ℝ) + 1 ≤ 2 ^ R := natCast_add_one_le_two_pow R
  have : 2 * ((R : ℝ) + 1) / 2 ^ kBis Q₀ I ≤ 1 / 2 ^ p := by
    rw [hK, div_le_div_iff₀ (by positivity) (by positivity)]
    clear_value R p T N M
    clear hT hN hR hB h hM hNR
    have hp0 : (0 : ℝ) < 2 ^ p := by positivity
    have hR0 : (0 : ℝ) < 2 ^ R := by positivity
    have h1 := mul_le_mul_of_nonneg_right hR2 hp0.le
    have h2 : 0 ≤ 2 ^ R * (2 : ℝ) ^ p := by positivity
    calc 2 * ((R : ℝ) + 1) * 2 ^ p = 2 * ((R + 1) * 2 ^ p) := by ring
      _ ≤ 2 * (2 ^ R * 2 ^ p) := by linarith
      _ ≤ 1 * (2 ^ p * 2 ^ R * 4) := by
        rw [one_mul, mul_comm ((2 : ℝ) ^ p) (2 ^ R)]
        linarith
  rw [show (2 : ℝ) / 2 ^ p = 1 / 2 ^ p + 1 / 2 ^ p by ring]
  linarith

end Gaussians

/-! ### The projections, one at a time -/

section Projections

variable (Q₀ : ℕ) (I : Instance) (cells : ℕ → ℕ)

/-- The first `m` projections. -/
def xiPre (m : ℕ) : List ℚ := (List.range m).foldl (xiStep Q₀ I cells) []

theorem xiPre_succ (m : ℕ) :
    xiPre Q₀ I cells (m + 1) =
      xiPre Q₀ I cells m ++ [xiNext Q₀ I cells (xiPre Q₀ I cells m) m] := by
  simp only [xiPre, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, xiStep]

theorem length_xiPre (m : ℕ) : (xiPre Q₀ I cells m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [xiPre_succ, List.length_append, ih, List.length_singleton]

theorem getD_xiPre {l m : ℕ} (hl : l < m) :
    (xiPre Q₀ I cells m).getD l 0 = xiNext Q₀ I cells (xiPre Q₀ I cells l) l := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [xiPre_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | rfl
    · rw [List.getD_append _ _ _ _ (by rw [length_xiPre]; exact h), ih h]
    · rw [List.getD_append_right _ _ _ _ (by rw [length_xiPre]), length_xiPre, Nat.sub_self]
      rfl

theorem getD_xiHat {k : ℕ} (hk : k < I.1) :
    (xiHat Q₀ I cells).getD k 0 = xiNext Q₀ I cells (xiPre Q₀ I cells k) k :=
  getD_xiPre Q₀ I cells hk

theorem sum_zipWith_mul (a b : List ℚ) (h : a.length = b.length) :
    (List.zipWith (· * ·) a b).sum = ∑ l ∈ range a.length, a.getD l 0 * b.getD l 0 := by
  induction a generalizing b with
  | nil => simp
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [List.zipWith_cons_cons, List.sum_cons, ih b h, List.length_cons, sum_range_succ',
        add_comm]
      simp

theorem length_coefL (k : ℕ) : (coefL Q₀ I k).length = k := by
  simp [coefL, SoS.PDTestRows.cof]

/-- The sum in the `k`-th projection. -/
theorem zipWith_coefL (k : ℕ) :
    ((coefL Q₀ I k).zipWith (· * ·) (xiPre Q₀ I cells k)).sum =
      ∑ l ∈ range k, (coefL Q₀ I k).getD l 0 * xiNext Q₀ I cells (xiPre Q₀ I cells l) l := by
  rw [sum_zipWith_mul _ _ (by rw [length_coefL, length_xiPre]), length_coefL]
  refine sum_congr rfl fun l hl ↦ ?_
  rw [getD_xiPre Q₀ I cells (mem_range.1 hl)]

end Projections

/-! ### The error of the projections -/

section XiError

/-- **Errors that grow geometrically**: if `eₖ ≤ ∑_{l<k} aₖₗ eₗ + E` with `∑_l aₖₗ ≤ C`, then
`eₖ ≤ E (1 + C)^k`. The recurrence may use the bound for the earlier errors. -/
theorem err_induct {n : ℕ} (e : ℕ → ℝ) (a : ℕ → ℕ → ℝ) {C E : ℝ} (hC : 0 ≤ C) (hE : 0 ≤ E)
    (ha0 : ∀ k l, 0 ≤ a k l) (ha : ∀ k < n, ∑ l ∈ range k, a k l ≤ C)
    (hrec : ∀ k < n, (∀ l < k, e l ≤ E * (1 + C) ^ l) →
      e k ≤ ∑ l ∈ range k, a k l * e l + E) :
    ∀ k < n, e k ≤ E * (1 + C) ^ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have IH : ∀ l < k, e l ≤ E * (1 + C) ^ l := fun l hl ↦ ih l hl (hl.trans hk)
    have h := hrec k hk IH
    rcases k with _ | m
    · simpa using h
    · have hpow : ∀ l < m + 1, E * (1 + C) ^ l ≤ E * (1 + C) ^ m := fun l hl ↦
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (by omega)) hE
      have hs : ∑ l ∈ range (m + 1), a (m + 1) l * e l ≤ C * (E * (1 + C) ^ m) := by
        calc ∑ l ∈ range (m + 1), a (m + 1) l * e l
            ≤ ∑ l ∈ range (m + 1), a (m + 1) l * (E * (1 + C) ^ m) :=
              sum_le_sum fun l hl ↦ mul_le_mul_of_nonneg_left
                ((IH l (mem_range.1 hl)).trans (hpow l (mem_range.1 hl))) (ha0 _ _)
          _ = (∑ l ∈ range (m + 1), a (m + 1) l) * (E * (1 + C) ^ m) := by rw [sum_mul]
          _ ≤ C * (E * (1 + C) ^ m) :=
              mul_le_mul_of_nonneg_right (ha _ hk) (by positivity)
      have h1 : E ≤ E * (1 + C) ^ m := le_mul_of_one_le_right hE (one_le_pow₀ (by linarith))
      rw [pow_succ]
      nlinarith

theorem norm_le_of_abs_le {m : ℕ} (g : EuclideanSpace ℝ (Fin m)) {R : ℝ} (hR : 0 ≤ R)
    (hg : ∀ k, |g k| ≤ R) : ‖g‖ ≤ m * R := by
  rw [EuclideanSpace.norm_eq]
  have h : ∑ i, ‖g i‖ ^ 2 ≤ (m * R) ^ 2 := by
    calc ∑ i, ‖g i‖ ^ 2 ≤ ∑ _i : Fin m, R ^ 2 := sum_le_sum fun i _ ↦ by
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hg i) 2
      _ = m * R ^ 2 := by simp
      _ ≤ (m * R) ^ 2 := by
        rw [mul_pow]
        rcases Nat.eq_zero_or_pos m with h | h
        · simp [h]
        · have : (1 : ℝ) ≤ m := by exact_mod_cast h
          have h2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right h2 (sq_nonneg R)
  calc √(∑ i, ‖g i‖ ^ 2) ≤ √((m * R) ^ 2) := Real.sqrt_le_sqrt h
    _ = m * R := Real.sqrt_sq (by positivity)

theorem abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  nlinarith [abs_nonneg x, sq_abs x, sq_nonneg (|x| - 1)]

variable {Q₀ : ℕ} {I : Instance}

/-- The vectors of the analysis are those of the algorithm's coefficients. -/
theorem vAlg_eq : vAlg Q₀ I = vec (coef (aMat Q₀ I)) (diagD (aMat Q₀ I)) := rfl

/-- The error per projection. -/
noncomputable def errE (Q₀ : ℕ) (I : Instance) : ℝ := ((rPar Q₀ I : ℝ) + 4) / 2 ^ pPar Q₀ I

/-- The bound on `∑_{l<k} |cₖₗ|`. -/
noncomputable def errC (Q₀ : ℕ) (I : Instance) : ℝ := I.1 + 2 / (tauS Q₀ I : ℝ)

theorem errC_nonneg : 0 ≤ errC Q₀ I := by
  have := tauS_pos (Q₀ := Q₀) (I := I)
  have : (0 : ℝ) < tauS Q₀ I := by exact_mod_cast this
  unfold errC
  positivity

theorem sum_abs_coef_le (hI : Valid I) (hQ : 10 ≤ Q₀) {k : ℕ} (hk : k < I.1) :
    ∑ l ∈ range k, |coef (aMat Q₀ I) k l| ≤ errC Q₀ I := by
  obtain ⟨-, -, h⟩ := sosVec_coef hI etaS_pos (gammaS_pos hI) tauS_pos (etaS_add_gammaS_le hQ)
    (tauS_le hQ) (solver_correct hI) hk
  calc ∑ l ∈ range k, |coef (aMat Q₀ I) k l|
      ≤ ∑ l ∈ range k, (1 + coef (aMat Q₀ I) k l ^ 2) :=
        sum_le_sum fun l _ ↦ abs_le_one_add_sq _
    _ = k + ∑ l ∈ range k, coef (aMat Q₀ I) k l ^ 2 := by
        rw [sum_add_distrib]; simp
    _ ≤ I.1 + 2 / (tauS Q₀ I : ℝ) := by
        have : (k : ℝ) ≤ I.1 := by exact_mod_cast hk.le
        have h' : ∑ l ∈ range k, coef (aMat Q₀ I) k l ^ 2 ≤ 2 / (tauS Q₀ I : ℝ) := by
          have := (Rat.cast_le (K := ℝ)).2 (le_refl (2 / tauS Q₀ I))
          push_cast at h this
          exact h
        linarith

/-- **The error of the projections**: on `|gₖ| ≤ R`, if the errors stay below `1` and the
projections below the clamp, `|ξ̂ₖ - ⟨vₖ, g⟩| ≤ E (1 + C)^k`. -/
theorem abs_xiNext_sub_le (hI : Valid I) (hQ : 10 ≤ Q₀) (g : EuclideanSpace ℝ (Fin I.1))
    (hg : ∀ k, |g k| ≤ rPar Q₀ I) (hsmall : errE Q₀ I * (1 + errC Q₀ I) ^ I.1 ≤ 1)
    (hclamp : I.1 * (rPar Q₀ I : ℝ) + errC Q₀ I + 2 ≤ 2 ^ pPar Q₀ I) :
    ∀ k < I.1, |(xiNext Q₀ I (cellsE Q₀ I g) (xiPre Q₀ I (cellsE Q₀ I g) k) k : ℝ) -
      ⟪vAlg Q₀ I k, g⟫| ≤ errE Q₀ I * (1 + errC Q₀ I) ^ k := by
  set cells := cellsE Q₀ I g
  set R := rPar Q₀ I
  set p := pPar Q₀ I
  set A := aMat Q₀ I
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hE : 0 ≤ errE Q₀ I := by unfold errE; positivity
  have hC := errC_nonneg (Q₀ := Q₀) (I := I)
  refine err_induct (fun k ↦ |(xiNext Q₀ I cells (xiPre Q₀ I cells k) k : ℝ) - ⟪vAlg Q₀ I k, g⟫|)
    (fun k l ↦ |coef A k l|) hC hE (fun _ _ ↦ abs_nonneg _)
    (fun k hk ↦ sum_abs_coef_le hI hQ hk) ?_
  intro k hk IH
  obtain ⟨hD0, hD1, -⟩ := sosVec_coef hI etaS_pos (gammaS_pos hI) tauS_pos
    (etaS_add_gammaS_le hQ) (tauS_le hQ) (solver_correct hI) hk
  -- The rational quantities of the step.
  set xh : ℕ → ℚ := fun l ↦ xiNext Q₀ I cells (xiPre Q₀ I cells l) l with hxh
  set gh : ℚ := gHat Q₀ I cells k
  set D' : ℚ := diagL Q₀ I k
  have hD' : (D' : ℝ) = diagD A k := diagL_eq Q₀ I hk
  have hD'0 : 0 ≤ D' := by
    have : (0 : ℝ) ≤ D' := by rw [hD']; exact hD0.le
    exact_mod_cast this
  set pre : ℚ := ∑ l ∈ range k, (coefL Q₀ I k).getD l 0 * xh l + sqrtP p D' * gh with hpre
  have hnext : xiNext Q₀ I cells (xiPre Q₀ I cells k) k = clamp (clampPar Q₀ I) (roundP p pre) := by
    rw [xiNext, zipWith_coefL]
  -- The ideal projection.
  have hgk := hg ⟨k, hk⟩
  have hξ : ⟪vAlg Q₀ I k, g⟫ = ∑ l ∈ range k, coef A k l * ⟪vAlg Q₀ I l, g⟫ +
      √(diagD A k) * g ⟨k, hk⟩ := by
    rw [vAlg_eq]; exact inner_vec_eq _ _ hk g
  -- The Gaussian term.
  have hgh := abs_gHat_sub_le g hk hgk
  have hsq := abs_sqrtP_sub_le p hD'0
  rw [hD'] at hsq
  have hghR : |(gh : ℝ)| ≤ R + 1 := by
    have h2p : (2 : ℝ) / 2 ^ p ≤ 1 := by
      rw [div_le_one hp]
      have : (2 : ℝ) ≤ 2 ^ 1 := by norm_num
      have h3 := three_le_zPar I
      exact this.trans (pow_le_pow_right₀ (by norm_num) (by simp only [p, pPar]; nlinarith))
    calc |(gh : ℝ)| = |((gh : ℝ) - g ⟨k, hk⟩) + g ⟨k, hk⟩| := by ring_nf
      _ ≤ |(gh : ℝ) - g ⟨k, hk⟩| + |g ⟨k, hk⟩| := abs_add_le _ _
      _ ≤ R + 1 := by linarith
  have hsqrtD : √(diagD A k) ≤ 1 := Real.sqrt_le_one.2 hD1
  have hgterm : |(sqrtP p D' : ℝ) * gh - √(diagD A k) * g ⟨k, hk⟩| ≤ (R + 3) / 2 ^ p := by
    have e : (sqrtP p D' : ℝ) * gh - √(diagD A k) * g ⟨k, hk⟩ =
        ((sqrtP p D' : ℝ) - √(diagD A k)) * gh + √(diagD A k) * ((gh : ℝ) - g ⟨k, hk⟩) := by ring
    rw [e]
    calc |((sqrtP p D' : ℝ) - √(diagD A k)) * gh + √(diagD A k) * ((gh : ℝ) - g ⟨k, hk⟩)|
        ≤ |((sqrtP p D' : ℝ) - √(diagD A k))| * |(gh : ℝ)| +
          √(diagD A k) * |(gh : ℝ) - g ⟨k, hk⟩| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ 1 / 2 ^ p * (R + 1) + 1 * (2 / 2 ^ p) := by
          gcongr
      _ = (R + 3) / 2 ^ p := by ring
  -- The sum term.
  have hcoef : ∀ l ∈ range k, (((coefL Q₀ I k).getD l 0 : ℚ) : ℝ) = coef A k l :=
    fun l hl ↦ coefL_eq Q₀ I hk (mem_range.1 hl)
  have hpre_cast : (pre : ℝ) = ∑ l ∈ range k, coef A k l * (xh l : ℝ) + sqrtP p D' * gh := by
    rw [hpre]
    push_cast
    congr 1
    exact sum_congr rfl fun l hl ↦ by rw [hcoef l hl]
  have hsum : |∑ l ∈ range k, coef A k l * (xh l : ℝ) -
      ∑ l ∈ range k, coef A k l * ⟪vAlg Q₀ I l, g⟫| ≤
      ∑ l ∈ range k, |coef A k l| * |(xh l : ℝ) - ⟪vAlg Q₀ I l, g⟫| := by
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun l _ ↦ ?_))
    rw [← mul_sub, abs_mul]
  have hpre_err : |(pre : ℝ) - ⟪vAlg Q₀ I k, g⟫| ≤
      ∑ l ∈ range k, |coef A k l| * |(xh l : ℝ) - ⟪vAlg Q₀ I l, g⟫| + (R + 3) / 2 ^ p := by
    rw [hpre_cast, hξ]
    have e : ∑ l ∈ range k, coef A k l * (xh l : ℝ) + sqrtP p D' * gh -
        (∑ l ∈ range k, coef A k l * ⟪vAlg Q₀ I l, g⟫ + √(diagD A k) * g ⟨k, hk⟩) =
        (∑ l ∈ range k, coef A k l * (xh l : ℝ) -
          ∑ l ∈ range k, coef A k l * ⟪vAlg Q₀ I l, g⟫) +
        ((sqrtP p D' : ℝ) * gh - √(diagD A k) * g ⟨k, hk⟩) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add hsum hgterm)
  -- The earlier errors are below `1`, so the sum is below `C`.
  have hsum1 : ∑ l ∈ range k, |coef A k l| * |(xh l : ℝ) - ⟪vAlg Q₀ I l, g⟫| ≤ errC Q₀ I := by
    calc ∑ l ∈ range k, |coef A k l| * |(xh l : ℝ) - ⟪vAlg Q₀ I l, g⟫|
        ≤ ∑ l ∈ range k, |coef A k l| * 1 := by
          refine sum_le_sum fun l hl ↦ mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine (IH l (mem_range.1 hl)).trans (le_trans ?_ hsmall)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith)
            ((mem_range.1 hl).trans hk).le) hE
      _ ≤ errC Q₀ I := by simpa using sum_abs_coef_le hI hQ hk
  -- Rounding.
  have hround : |(roundP p pre : ℝ) - pre| ≤ 1 / 2 ^ p := by
    have := abs_roundP_sub_le p pre
    have h' := (Rat.cast_le (K := ℝ)).2 this
    push_cast at h'
    exact h'
  -- No clamping.
  have hξk : |⟪vAlg Q₀ I k, g⟫| ≤ I.1 * R := by
    have hu := (vAlg_spec hI hQ).1 k hk
    calc |⟪vAlg Q₀ I k, g⟫| ≤ ‖vAlg Q₀ I k‖ * ‖g‖ := abs_real_inner_le_norm _ _
      _ = ‖g‖ := by rw [hu, one_mul]
      _ ≤ I.1 * R := norm_le_of_abs_le g (by positivity) hg
  have hR3 : ((R : ℝ) + 3) / 2 ^ p + 1 / 2 ^ p ≤ 1 := by
    have : errE Q₀ I ≤ 1 := le_trans (le_mul_of_one_le_right hE
      (one_le_pow₀ (by linarith))) hsmall
    unfold errE at this
    rw [← add_div]; linarith [show ((R : ℝ) + 3 + 1) / 2 ^ p = (R + 4) / 2 ^ p by ring_nf]
  have hclamp' : |(roundP p pre : ℚ)| ≤ clampPar Q₀ I := by
    have : |(roundP p pre : ℝ)| ≤ 2 ^ p := by
      calc |(roundP p pre : ℝ)| = |((roundP p pre : ℝ) - pre) + ((pre : ℝ) - ⟪vAlg Q₀ I k, g⟫) +
            ⟪vAlg Q₀ I k, g⟫| := by ring_nf
        _ ≤ |(roundP p pre : ℝ) - pre| + |(pre : ℝ) - ⟪vAlg Q₀ I k, g⟫| +
            |⟪vAlg Q₀ I k, g⟫| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ 2 ^ p := by linarith
    have h2 : ((2 ^ p : ℚ) : ℝ) = 2 ^ p := by push_cast; ring
    rw [clampPar, ← Rat.cast_le (K := ℝ), Rat.cast_abs, h2]
    exact this
  rw [hnext, clamp_of_abs_le hclamp']
  calc |(roundP p pre : ℝ) - ⟪vAlg Q₀ I k, g⟫|
      = |((roundP p pre : ℝ) - pre) + ((pre : ℝ) - ⟪vAlg Q₀ I k, g⟫)| := by ring_nf
    _ ≤ |(roundP p pre : ℝ) - pre| + |(pre : ℝ) - ⟪vAlg Q₀ I k, g⟫| := abs_add_le _ _
    _ ≤ ∑ l ∈ range k, |coef A k l| * |(xh l : ℝ) - ⟪vAlg Q₀ I l, g⟫| + errE Q₀ I := by
        unfold errE
        have : ((R : ℝ) + 4) / 2 ^ p = (R + 3) / 2 ^ p + 1 / 2 ^ p := by ring
        rw [this]
        linarith

end XiError

/-! ### The error of the votes -/

section VoteError

theorem abs_Phi_sub_le (x y : ℝ) : |Phi x - Phi y| ≤ |x - y| / 2 := by
  wlog h : x ≤ y generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x]; exact this y x (le_of_not_ge h)
  have hmono : Phi x ≤ Phi y := strictMono_Phi.monotone h
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), neg_sub, neg_sub]
  unfold Phi
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real,
    ← MeasureTheory.measureReal_sdiff (Set.Iic_subset_Iic.2 h) measurableSet_Iic]
  calc (ProbabilityTheory.gaussianReal 0 1).real (Set.Iic y \ Set.Iic x)
      ≤ (ProbabilityTheory.gaussianReal 0 1).real {z | |z - (x + y) / 2| ≤ (y - x) / 2} := by
        refine MeasureTheory.measureReal_mono (fun z hz ↦ ?_)
        simp only [Set.mem_sdiff, Set.mem_Iic, not_le] at hz
        simp only [Set.mem_ofPred_eq, abs_le]
        constructor <;> linarith
    _ ≤ (y - x) / 2 := gaussianReal_abs_sub_le _ (by linarith)

variable {Q₀ : ℕ} {I : Instance}

theorem four_le_pPar : 4 ≤ pPar Q₀ I := by
  unfold pPar
  have : 1 ≤ (zPar I + Q₀) ^ 2 := Nat.one_le_pow _ _ (by have := three_le_zPar I; omega)
  omega

theorem inv_two_pow_pPar_le : (1 : ℝ) / 2 ^ pPar Q₀ I ≤ 1 / 16 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
  calc (16 : ℝ) = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ pPar Q₀ I := pow_le_pow_right₀ (by norm_num) four_le_pPar

theorem kPar_pos (I : Instance) : (0 : ℝ) < kPar I := by
  have := five_le_kPar I
  exact_mod_cast (show 0 < kPar I by omega)

theorem etaQ_cast : (etaQ I : ℝ) = ((kPar I : ℝ) ^ 2 - 1) / ((kPar I : ℝ) ^ 2 + 1) := by
  simp [etaQ]

theorem etaQ_nonneg : (0 : ℝ) ≤ etaQ I := by
  rw [etaQ_cast]
  have : (5 : ℝ) ≤ kPar I := by exact_mod_cast five_le_kPar I
  apply div_nonneg <;> nlinarith

theorem etaQ_lt_one : (etaQ I : ℝ) < 1 := by
  rw [etaQ_cast, div_lt_one (by positivity)]
  linarith

/-- `η / √(1 - η²) = (k² - 1)/(2k)`. -/
theorem etaQ_div_sqrt : (etaQ I : ℝ) / √(1 - (etaQ I : ℝ) ^ 2) = ratioQ I := by
  have hk := kPar_pos I
  have hs : √(1 - (etaQ I : ℝ) ^ 2) = 2 * (kPar I : ℝ) / ((kPar I : ℝ) ^ 2 + 1) := by
    rw [etaQ_cast]
    have h : 1 - (((kPar I : ℝ) ^ 2 - 1) / ((kPar I : ℝ) ^ 2 + 1)) ^ 2 =
        (2 * (kPar I : ℝ) / ((kPar I : ℝ) ^ 2 + 1)) ^ 2 := by
      field_simp; ring
    rw [h, Real.sqrt_sq (by positivity)]
  rw [hs, etaQ_cast, ratioQ]
  push_cast
  field_simp

theorem ratioQ_nonneg : (0 : ℝ) ≤ ratioQ I := by
  have : (5 : ℝ) ≤ kPar I := by exact_mod_cast five_le_kPar I
  rw [ratioQ]; push_cast
  apply div_nonneg <;> nlinarith

theorem ratioQ_le : (ratioQ I : ℝ) ≤ kPar I / 2 := by
  have hk := kPar_pos I
  rw [ratioQ]; push_cast
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The error of a quotient: if `ŝ ≤ s` is within `δ ≤ 1/16` of `s ≥ 3/5`, `|â - a| ≤ 2ε` and
`|a| ≤ 2M`, then `|â/ŝ - a/s| ≤ 4ε + 7Mδ`. -/
theorem abs_div_sub_div_le {s sh a ah ε δ M : ℝ} (hs : 3 / 5 ≤ s) (hsh1 : sh ≤ s)
    (hsh2 : s - δ ≤ sh) (hδ : δ ≤ 1 / 16) (hda : |ah - a| ≤ 2 * ε) (ha : |a| ≤ 2 * M) :
    |ah / sh - a / s| ≤ 4 * ε + 7 * M * δ := by
  have hsh0 : (0 : ℝ) < sh := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have hε : 0 ≤ ε := by linarith [abs_nonneg (ah - a)]
  have hM : 0 ≤ M := by linarith [abs_nonneg a]
  have hd0 : 0 ≤ s - sh := by linarith
  have e : ah / sh - a / s = (ah - a) / sh + a * (s - sh) / (sh * s) := by
    field_simp; ring
  rw [e]
  have t1 : |(ah - a) / sh| ≤ 4 * ε := by
    rw [abs_div, abs_of_pos hsh0, div_le_iff₀ hsh0]
    have : 2 * ε ≤ 4 * ε * sh := by
      have := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ sh by linarith)
        (show 0 ≤ 4 * ε by linarith)
      linarith
    linarith
  have t2 : |a * (s - sh) / (sh * s)| ≤ 7 * M * δ := by
    have hss : (3 : ℝ) / 10 ≤ sh * s :=
      calc (3 : ℝ) / 10 = 1 / 2 * (3 / 5) := by norm_num
        _ ≤ sh * s := mul_le_mul (by linarith) hs (by norm_num) hsh0.le
    rw [abs_div, abs_mul, abs_of_nonneg hd0, abs_of_pos (mul_pos hsh0 hs0),
      div_le_iff₀ (mul_pos hsh0 hs0)]
    have h1 : |a| * (s - sh) ≤ 2 * M * δ :=
      mul_le_mul ha (by linarith) hd0 (by linarith)
    have h2 : 0 ≤ 7 * M * δ := by
      have : 0 ≤ δ := by linarith
      positivity
    have h3 := mul_le_mul_of_nonneg_left hss h2
    linarith
  exact (abs_add_le _ _).trans (add_le_add t1 t2)

/-- The size of the quotient: `|â/ŝ| ≤ 4M` when `|a| ≤ 2M`, `M ≥ 2`, and the error is small. -/
theorem abs_div_le_of_err {s sh a ah ε c M : ℝ} (hs : 3 / 5 ≤ s) (ha : |a| ≤ 2 * M)
    (hdh : |ah / sh - a / s| ≤ 4 * ε + c) (hε : ε ≤ 1 / 8) (hc : c ≤ 1 / 2) (hM : 2 ≤ M) :
    |ah / sh| ≤ 4 * M := by
  have hs0 : (0 : ℝ) < s := by linarith
  have h1 : |a / s| ≤ 2 * M * (5 / 3) := by
    rw [abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
    have := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 2 * M * (5 / 3) by linarith)
    linarith
  have h2 := abs_add_le (ah / sh - a / s) (a / s)
  rw [sub_add_cancel] at h2
  linarith

/-- The direction `uᵢⱼ` of an out-edge `e = (j, b, w)` of `i`: `⟨uᵢⱼ, g⟩ = (b ξⱼ - ρ ξᵢ)/s`. -/
theorem inner_dirVec_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ℕ → E)
    (i j : ℕ) (b : Bool) (g : E) :
    ⟪dirVec v i j b, g⟫ = (bsign b * ⟪v j, g⟫ - rho v i j b * ⟪v i, g⟫) /
      √(1 - rho v i j b ^ 2) := by
  rw [dirVec, real_inner_smul_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  ring

/-- **The error of one term of the vote**: for an out-edge `e = (j, b, w)` of `i` in the window,
`2 Φ̂(η ĥₑ / √(1 - η²)) - 1` is close to `s_η(hₑ)`. -/
theorem abs_edge_sub_le (hI : Valid I) (hQ : 10 ≤ Q₀) (g : EuclideanSpace ℝ (Fin I.1))
    (hg : ∀ k, |g k| ≤ rPar Q₀ I) (xi : List ℚ) {ε : ℝ}
    (hξ : ∀ k < I.1, |(xi.getD k 0 : ℝ) - ⟪vAlg Q₀ I k, g⟫| ≤ ε) (hε : ε ≤ 1 / 8)
    (hpR : 7 * I.1 * (rPar Q₀ I : ℝ) / 2 ^ pPar Q₀ I ≤ 1 / 2)
    (hN : 3 * ((ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I)) ^ 2 ≤ nSer Q₀ I) {i : ℕ}
    {e : ℕ × Bool × ℚ} (he : e ∈ outEdges (windowSet (vAlg Q₀ I) I) i) :
    |((2 * phiQ (tPar Q₀ I) (nSer Q₀ I) (ratioQ I * hHat Q₀ I xi i e) - 1 : ℚ) : ℝ) -
      smoothSign (etaQ I) ⟪dirVec (vAlg Q₀ I) i e.1 e.2.1, g⟫| ≤
      2 * ((ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I) / 2 ^ nSer Q₀ I + 2 / 2 ^ tPar Q₀ I +
        (ratioQ I : ℝ) * (4 * ε + 7 * I.1 * rPar Q₀ I / 2 ^ pPar Q₀ I) / 2) := by
  obtain ⟨hi, hj, -, hw1, hw2⟩ := outEdge_window (vAlg Q₀ I) hI he
  have hunit := (vAlg_spec hI hQ).1
  -- `ρ`, exactly, and `s = √(1 - ρ²) ≥ 3/5` with its approximation `ŝ`.
  obtain ⟨ρq, hρq⟩ : ∃ ρq : ℚ, ρq = SDP.objective.bsignQ e.2.1 * aQ Q₀ I i e.1 := ⟨_, rfl⟩
  have hρ : (ρq : ℝ) = rho (vAlg Q₀ I) i e.1 e.2.1 := by
    rw [hρq, rho, (vAlg_spec hI hQ).2.1 i e.1 hi hj]; push_cast; rw [SDP.bsignQ_cast]
  rw [← hρ] at hw1 hw2
  have hρ0 : (0 : ℝ) ≤ ρq := by linarith
  have hρ2 : (ρq : ℝ) ^ 2 ≤ 16 / 25 :=
    (pow_le_pow_left₀ hρ0 hw2.le 2).trans_eq (by norm_num)
  have h1ρ : (0 : ℚ) ≤ 1 - ρq ^ 2 := by
    have : (0 : ℝ) ≤ 1 - (ρq : ℝ) ^ 2 := by linarith
    exact_mod_cast this
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = √(1 - (ρq : ℝ) ^ 2) := ⟨_, rfl⟩
  have hs35 : 3 / 5 ≤ s := by
    rw [hs, Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hsh_le : (sqrtP (pPar Q₀ I) (1 - ρq ^ 2) : ℝ) ≤ s := by
    have := sqrtP_le_sqrt (pPar Q₀ I) h1ρ; push_cast at this; rw [hs]; exact this
  have hsh_ge : s - 1 / 2 ^ pPar Q₀ I ≤ sqrtP (pPar Q₀ I) (1 - ρq ^ 2) := by
    have := abs_sqrtP_sub_le (pPar Q₀ I) h1ρ; push_cast at this
    rw [hs]; linarith [(abs_le.1 this).1]
  -- The ideal `h` and the computed `ĥ`.
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = I.1 * rPar Q₀ I := ⟨_, rfl⟩
  have hξb : ∀ k < I.1, |⟪vAlg Q₀ I k, g⟫| ≤ M := fun k hk ↦ by
    calc |⟪vAlg Q₀ I k, g⟫| ≤ ‖vAlg Q₀ I k‖ * ‖g‖ := abs_real_inner_le_norm _ _
      _ = ‖g‖ := by rw [hunit k hk, one_mul]
      _ ≤ M := hMdef ▸ norm_le_of_abs_le g (by positivity) hg
  have hb : |bsign e.2.1| = 1 := by rcases bsign_cases e.2.1 with h | h <;> rw [h] <;> simp
  have hρabs : |(ρq : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = bsign e.2.1 * ⟪vAlg Q₀ I e.1, g⟫ - ρq * ⟪vAlg Q₀ I i, g⟫ :=
    ⟨_, rfl⟩
  obtain ⟨ah, hah⟩ : ∃ ah : ℝ,
      ah = bsign e.2.1 * (xi.getD e.1 0 : ℝ) - ρq * (xi.getD i 0 : ℝ) := ⟨_, rfl⟩
  have hh : ⟪dirVec (vAlg Q₀ I) i e.1 e.2.1, g⟫ = a / s := by
    rw [inner_dirVec_eq, ← hρ, ha, hs]
  have hhh : (hHat Q₀ I xi i e : ℝ) = ah / sqrtP (pPar Q₀ I) (1 - ρq ^ 2) := by
    rw [hHat, hah, hρq]
    push_cast
    rw [SDP.bsignQ_cast]
  have two_terms : ∀ x y z w : ℝ, |x| ≤ 1 → |z| ≤ 1 →
      |x * y - z * w| ≤ |y| + |w| := fun x y z w hx hz ↦ by
    calc |x * y - z * w| ≤ |x| * |y| + |z| * |w| := by
          refine (abs_sub _ _).trans ?_; rw [abs_mul, abs_mul]
      _ ≤ 1 * |y| + 1 * |w| := by gcongr
      _ = |y| + |w| := by ring
  have hda : |ah - a| ≤ 2 * ε := by
    have e1 : ah - a = bsign e.2.1 * ((xi.getD e.1 0 : ℝ) - ⟪vAlg Q₀ I e.1, g⟫) -
        ρq * ((xi.getD i 0 : ℝ) - ⟪vAlg Q₀ I i, g⟫) := by rw [hah, ha]; ring
    rw [e1]
    have := two_terms (bsign e.2.1) ((xi.getD e.1 0 : ℝ) - ⟪vAlg Q₀ I e.1, g⟫) ρq
      ((xi.getD i 0 : ℝ) - ⟪vAlg Q₀ I i, g⟫) hb.le hρabs
    linarith [hξ e.1 hj, hξ i hi]
  have hah_abs : |a| ≤ 2 * M := by
    rw [ha]
    have := two_terms (bsign e.2.1) ⟪vAlg Q₀ I e.1, g⟫ ρq ⟪vAlg Q₀ I i, g⟫ hb.le hρabs
    linarith [hξb e.1 hj, hξb i hi]
  have hp4 : (1 : ℝ) / 2 ^ pPar Q₀ I ≤ 1 / 16 := inv_two_pow_pPar_le
  have hdh := abs_div_sub_div_le hs35 hsh_le hsh_ge hp4 hda hah_abs
  have e7 : 7 * M * (1 / 2 ^ pPar Q₀ I) = 7 * I.1 * rPar Q₀ I / 2 ^ pPar Q₀ I := by
    rw [hMdef]; ring
  rw [e7] at hdh
  -- The arguments of `Φ`.
  have hrat := ratioQ_nonneg (I := I)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (ratioQ I : ℝ) * (a / s) := ⟨_, rfl⟩
  have hxh : ((ratioQ I * hHat Q₀ I xi i e : ℚ) : ℝ) =
      (ratioQ I : ℝ) * (ah / sqrtP (pPar Q₀ I) (1 - ρq ^ 2)) := by
    push_cast; rw [hhh]
  have hdx : |((ratioQ I * hHat Q₀ I xi i e : ℚ) : ℝ) - x| ≤
      (ratioQ I : ℝ) * (4 * ε + 7 * I.1 * rPar Q₀ I / 2 ^ pPar Q₀ I) := by
    rw [hxh, hx, ← mul_sub, abs_mul, abs_of_nonneg hrat]
    exact mul_le_mul_of_nonneg_left hdh hrat
  have hM2 : (2 : ℝ) ≤ M := by
    have h1 : (1 : ℝ) ≤ I.1 := by exact_mod_cast (show 1 ≤ I.1 by omega)
    have h2 : (2 : ℝ) ≤ rPar Q₀ I := by exact_mod_cast two_le_rPar Q₀ I
    rw [hMdef]
    calc (2 : ℝ) = 1 * 2 := by norm_num
      _ ≤ I.1 * rPar Q₀ I := mul_le_mul h1 h2 (by norm_num) (by linarith)
  have hxh_abs : |((ratioQ I * hHat Q₀ I xi i e : ℚ) : ℝ)| ≤
      (ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I) := by
    rw [hxh, abs_mul, abs_of_nonneg hrat]
    refine mul_le_mul_of_nonneg_left ?_ hrat
    have := abs_div_le_of_err hs35 hah_abs hdh hε hpR hM2
    rw [hMdef] at this
    linarith
  -- `Φ̂` and `Φ`.
  have hT5 : 5 ≤ tPar Q₀ I := by unfold tPar; omega
  have hN' : 3 * (((ratioQ I * hHat Q₀ I xi i e : ℚ) : ℝ)) ^ 2 ≤ nSer Q₀ I := by
    refine le_trans ?_ hN
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hxh_abs 2
    rw [sq_abs] at h1
    linarith
  have hphi := abs_phiQ_sub_le (n := tPar Q₀ I) (N := nSer Q₀ I) hT5 hN'
  have hss : smoothSign (etaQ I) ⟪dirVec (vAlg Q₀ I) i e.1 e.2.1, g⟫ = 2 * Phi x - 1 := by
    have e1 : (etaQ I : ℝ) * (a / s) / √(1 - (etaQ I : ℝ) ^ 2) = x := by
      rw [mul_comm, mul_div_assoc, etaQ_div_sqrt, mul_comm, hx]
    rw [smoothSign_eq_Phi etaQ_nonneg etaQ_lt_one, hh, e1]
  rw [hss]
  obtain ⟨xh, hxhq⟩ : ∃ xh : ℚ, xh = ratioQ I * hHat Q₀ I xi i e := ⟨_, rfl⟩
  rw [← hxhq] at hphi hdx hxh_abs ⊢
  push_cast
  have hlip := abs_Phi_sub_le (xh : ℝ) x
  have e2 : 2 * (phiQ (tPar Q₀ I) (nSer Q₀ I) xh : ℝ) - 1 - (2 * Phi x - 1) =
      2 * (((phiQ (tPar Q₀ I) (nSer Q₀ I) xh : ℝ) - Phi xh) + (Phi xh - Phi x)) := by ring
  rw [e2, abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (abs_add_le _ _).trans ?_
  have h2N : (0 : ℝ) < 2 ^ nSer Q₀ I := by positivity
  have t1 : |(xh : ℝ)| / 2 ^ nSer Q₀ I ≤
      (ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I) / 2 ^ nSer Q₀ I :=
    div_le_div_of_nonneg_right hxh_abs h2N.le
  have t2 : |(xh : ℝ) - x| / 2 ≤
      (ratioQ I : ℝ) * (4 * ε + 7 * I.1 * rPar Q₀ I / 2 ^ pPar Q₀ I) / 2 :=
    div_le_div_of_nonneg_right hdx (by norm_num)
  linarith only [hphi, hlip, t1, t2]

theorem list_abs_sum_le {α : Type*} (l : List α) (f b : α → ℝ) (h : ∀ x ∈ l, |f x| ≤ b x) :
    |(l.map f).sum| ≤ (l.map b).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (h a List.mem_cons_self)
      (ih fun x hx ↦ h x (List.mem_cons_of_mem a hx)))

theorem sum_fin_getElem {α : Type*} (l : List α) (F : α → ℝ) :
    ∑ k : Fin l.length, F l[k] = (l.map F).sum := by
  rw [← List.sum_ofFn, ← List.ofFn_getElem_eq_map l F]
  rfl

theorem wDegQ_cast (hI : Valid I) (hQ : 10 ≤ Q₀) (i : ℕ) :
    (wDegQ Q₀ I i : ℝ) = wdeg (windowSet (vAlg Q₀ I) I) i := by
  rw [wDegQ, wdeg, winList_eq hI hQ, Rat.cast_list_sum, List.map_map]
  rfl

/-- **The error of the vote**: `|f̂ᵢ - fᵢ(g)|` is at most the error of one term. -/
theorem abs_fHat_sub_le (hI : Valid I) (hQ : 10 ≤ Q₀) (g : EuclideanSpace ℝ (Fin I.1))
    (hg : ∀ k, |g k| ≤ rPar Q₀ I) (xi : List ℚ) {ε : ℝ}
    (hξ : ∀ k < I.1, |(xi.getD k 0 : ℝ) - ⟪vAlg Q₀ I k, g⟫| ≤ ε) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8)
    (hpR : 7 * I.1 * (rPar Q₀ I : ℝ) / 2 ^ pPar Q₀ I ≤ 1 / 2)
    (hN : 3 * ((ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I)) ^ 2 ≤ nSer Q₀ I) (i : ℕ) :
    |(fHat Q₀ I xi i : ℝ) - fvote (vAlg Q₀ I) (windowSet (vAlg Q₀ I) I) (etaQ I) i g| ≤
      2 * ((ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I) / 2 ^ nSer Q₀ I + 2 / 2 ^ tPar Q₀ I +
        (ratioQ I : ℝ) * (4 * ε + 7 * I.1 * rPar Q₀ I / 2 ^ pPar Q₀ I) / 2) := by
  set B := 2 * ((ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I) / 2 ^ nSer Q₀ I + 2 / 2 ^ tPar Q₀ I +
    (ratioQ I : ℝ) * (4 * ε + 7 * I.1 * rPar Q₀ I / 2 ^ pPar Q₀ I) / 2) with hB
  set T := windowSet (vAlg Q₀ I) I
  set W := wdeg T i
  have hT : ∀ c ∈ T, 0 ≤ c.2.2 := fun c hc ↦ (windowSet_valid _ hI c hc).2.2
  have hW : 0 ≤ W := wdeg_nonneg hT i
  set φ : ℕ × Bool × ℚ → ℝ := fun e ↦
    (((2 * phiQ (tPar Q₀ I) (nSer Q₀ I) (ratioQ I * hHat Q₀ I xi i e) - 1 : ℚ) : ℝ))
  set σ : ℕ × Bool × ℚ → ℝ := fun e ↦ smoothSign (etaQ I) ⟪dirVec (vAlg Q₀ I) i e.1 e.2.1, g⟫
  have hf : (fHat Q₀ I xi i : ℝ) = ((outEdges T i).map fun e ↦ (e.2.2 : ℝ) / W * φ e).sum := by
    rw [fHat, Rat.cast_list_sum, List.map_map, winList_eq hI hQ]
    congr 1
    refine List.map_congr_left fun e _ ↦ ?_
    simp only [Function.comp_apply, φ]
    push_cast
    rw [wDegQ_cast hI hQ]
  have hv : fvote (vAlg Q₀ I) T (etaQ I) i g =
      ((outEdges T i).map fun e ↦ (e.2.2 : ℝ) / W * σ e).sum := by
    rw [fvote, vote, ← sum_fin_getElem]
    rfl
  rw [hf, hv, ← list_sum_map_sub]
  have hterm : ∀ e ∈ outEdges T i, |(e.2.2 : ℝ) / W * φ e - (e.2.2 : ℝ) / W * σ e| ≤
      (e.2.2 : ℝ) / W * B := by
    intro e he
    rw [← mul_sub, abs_mul, abs_of_nonneg (div_nonneg (outEdges_w_nonneg hT he) hW)]
    exact mul_le_mul_of_nonneg_left (abs_edge_sub_le hI hQ g hg xi hξ hε hpR hN he)
      (div_nonneg (outEdges_w_nonneg hT he) hW)
  have hB0 : 0 ≤ B := by
    have := ratioQ_nonneg (I := I)
    rw [hB]; positivity
  refine (list_abs_sum_le _ _ _ hterm).trans ?_
  have hsum : ((outEdges T i).map fun e ↦ (e.2.2 : ℝ) / W * B).sum = W / W * B := by
    have : (fun e : ℕ × Bool × ℚ ↦ (e.2.2 : ℝ) / W * B) = fun e ↦ (e.2.2 : ℝ) * (W⁻¹ * B) := by
      funext e; rw [div_eq_mul_inv, mul_assoc]
    rw [this, List.sum_map_mul_right, div_eq_mul_inv, mul_assoc]
    rfl
  rw [hsum]
  rcases eq_or_lt_of_le hW with h | h
  · rw [← h]; simp [hB0]
  · rw [div_self h.ne', one_mul]

end VoteError

/-! ### The numbers -/

section Numbers

variable {Q₀ : ℕ} {I : Instance}

/-- `V = 2^b` for `b = Z + Q₀`. -/
noncomputable abbrev bigV (Q₀ : ℕ) (I : Instance) : ℝ := 2 ^ qPar Q₀ I

/-- `U = 2^(b²)`; the precision is `2^p = U⁴` and the final accuracy `1/U`. -/
noncomputable abbrev bigU (Q₀ : ℕ) (I : Instance) : ℝ := 2 ^ (qPar Q₀ I ^ 2)

theorem qPar_ge (hQ : 10 ≤ Q₀) : 13 ≤ qPar Q₀ I := by
  have := three_le_zPar I; unfold qPar; omega

theorem two_pow_pPar : (2 : ℝ) ^ pPar Q₀ I = bigU Q₀ I ^ 4 := by
  rw [bigU, ← pow_mul, pPar, qPar, mul_comm]

theorem bigV_ge (hQ : 10 ≤ Q₀) : (8192 : ℝ) ≤ bigV Q₀ I := by
  calc (8192 : ℝ) = 2 ^ 13 := by norm_num
    _ ≤ 2 ^ qPar Q₀ I := pow_le_pow_right₀ (by norm_num) (qPar_ge hQ)

theorem bigV_cube (hQ : 10 ≤ Q₀) : 8192 * bigV Q₀ I ^ 3 ≤ bigV Q₀ I ^ 4 := by
  rw [pow_succ, mul_comm]
  exact mul_le_mul_of_nonneg_left (bigV_ge hQ) (by positivity)

theorem bigV_le_cube (hQ : 10 ≤ Q₀) : bigV Q₀ I ≤ bigV Q₀ I ^ 3 :=
  le_self_pow₀ (by have := bigV_ge (I := I) hQ; linarith) (by norm_num)

theorem bigV_le_bigU : bigV Q₀ I ≤ bigU Q₀ I := by
  rw [bigV, bigU]
  exact pow_le_pow_right₀ (by norm_num) (Nat.le_self_pow (by norm_num) _)

theorem bigU_ge (hQ : 10 ≤ Q₀) : bigV Q₀ I ^ 6 ≤ bigU Q₀ I := by
  rw [bigV, bigU, ← pow_mul]
  refine pow_le_pow_right₀ (by norm_num) ?_
  have := qPar_ge (I := I) hQ
  nlinarith

theorem zPar_le_bigV : (zPar I : ℝ) ≤ bigV Q₀ I := by
  have h1 : (zPar I : ℝ) ≤ 2 ^ zPar I := by
    have := natCast_add_one_le_two_pow (zPar I); linarith
  exact h1.trans (pow_le_pow_right₀ (by norm_num) (by unfold qPar; omega))

theorem n_le_bigV : (I.1 : ℝ) ≤ bigV Q₀ I := by
  have : (I.1 : ℝ) ≤ zPar I := by exact_mod_cast (n_lt_zPar I).le
  exact this.trans zPar_le_bigV

theorem rPar_le_bigV : (rPar Q₀ I : ℝ) ≤ bigV Q₀ I ^ 2 := by
  have h1 : (zPar I : ℝ) ≤ 2 ^ zPar I := by
    have := natCast_add_one_le_two_pow (zPar I); linarith
  have h2 : (rPar Q₀ I : ℝ) = (zPar I : ℝ) ^ 2 * 2 ^ Q₀ := by simp [rPar]
  rw [h2, bigV, ← pow_mul]
  calc (zPar I : ℝ) ^ 2 * 2 ^ Q₀ ≤ (2 ^ zPar I) ^ 2 * 2 ^ Q₀ := by gcongr
    _ = 2 ^ (2 * zPar I + Q₀) := by rw [← pow_mul, pow_add, mul_comm (zPar I)]
    _ ≤ 2 ^ (qPar Q₀ I * 2) := pow_le_pow_right₀ (by norm_num) (by unfold qPar; omega)

theorem zPar_sq_le_rPar : (zPar I : ℝ) ^ 2 ≤ rPar Q₀ I := by
  have : (rPar Q₀ I : ℝ) = (zPar I : ℝ) ^ 2 * 2 ^ Q₀ := by simp [rPar]
  rw [this]
  exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))

theorem tauS_cast : (tauS Q₀ I : ℝ) = 1 / bigV Q₀ I := by simp [tauS, bigV]

theorem ratioQ_le_z : (ratioQ I : ℝ) ≤ 11 * zPar I := by
  have h1 := ratioQ_le (I := I)
  have h2 : (kPar I : ℝ) ≤ 16 * zPar I + 5 := by
    have := kPar_le I
    have := lPar_le_zPar I
    exact_mod_cast (show kPar I ≤ 16 * zPar I + 5 by omega)
  have h3 : (3 : ℝ) ≤ zPar I := by exact_mod_cast three_le_zPar I
  linarith

theorem errC_le (hQ : 10 ≤ Q₀) : 1 + errC Q₀ I ≤ 4 * bigV Q₀ I := by
  rw [errC, tauS_cast]
  have := n_le_bigV (Q₀ := Q₀) (I := I)
  have := bigV_ge (Q₀ := Q₀) (I := I) hQ
  rw [div_div_eq_mul_div, div_one]
  linarith

/-- The error of the projections, `E (1 + C)^n ≤ 2V⁴/U³`. -/
theorem errXi_le (hQ : 10 ≤ Q₀) :
    errE Q₀ I * (1 + errC Q₀ I) ^ I.1 ≤ 2 * bigV Q₀ I ^ 4 / bigU Q₀ I ^ 3 := by
  have hV := bigV_ge (Q₀ := Q₀) (I := I) hQ
  have hU : 0 < bigU Q₀ I := by positivity
  have hpow : (1 + errC Q₀ I) ^ I.1 ≤ bigV Q₀ I ^ 2 * bigU Q₀ I := by
    have h1 : (1 + errC Q₀ I) ^ I.1 ≤ (4 * bigV Q₀ I) ^ I.1 :=
      pow_le_pow_left₀ (by have := errC_nonneg (Q₀ := Q₀) (I := I); linarith) (errC_le hQ) _
    have h2 : (4 * bigV Q₀ I) ^ I.1 ≤ (4 * bigV Q₀ I) ^ qPar Q₀ I :=
      pow_le_pow_right₀ (by linarith) (by have := n_lt_zPar I; unfold qPar; omega)
    have h3 : (4 * bigV Q₀ I) ^ qPar Q₀ I = bigV Q₀ I ^ 2 * bigU Q₀ I := by
      rw [mul_pow, bigV, bigU, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul,
        sq (qPar Q₀ I), mul_comm 2]
    linarith
  have hE : errE Q₀ I ≤ 2 * bigV Q₀ I ^ 2 / bigU Q₀ I ^ 4 := by
    rw [errE, two_pow_pPar]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have := rPar_le_bigV (Q₀ := Q₀) (I := I)
    nlinarith
  have hE0 : 0 ≤ errE Q₀ I := by unfold errE; positivity
  have hC0 : 0 ≤ (1 + errC Q₀ I) ^ I.1 :=
    pow_nonneg (by have := errC_nonneg (Q₀ := Q₀) (I := I); linarith) _
  calc errE Q₀ I * (1 + errC Q₀ I) ^ I.1
      ≤ (2 * bigV Q₀ I ^ 2 / bigU Q₀ I ^ 4) * (bigV Q₀ I ^ 2 * bigU Q₀ I) :=
        mul_le_mul hE hpow hC0 (by positivity)
    _ = 2 * bigV Q₀ I ^ 4 / bigU Q₀ I ^ 3 := by field_simp

theorem errXi_le' (hQ : 10 ≤ Q₀) : 2 * bigV Q₀ I ^ 4 / bigU Q₀ I ^ 3 ≤ 1 / 8 := by
  have hV := bigV_ge (Q₀ := Q₀) (I := I) hQ
  have hU := bigU_ge (Q₀ := Q₀) (I := I) hQ
  have hU0 : 0 < bigU Q₀ I := by positivity
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : bigV Q₀ I ^ 4 ≤ bigU Q₀ I := le_trans (pow_le_pow_right₀ (by linarith) (by norm_num)) hU
  have h2 : (16 : ℝ) ≤ bigU Q₀ I := by nlinarith [pow_le_pow_left₀ (by norm_num) hV 4]
  have h3 : (16 : ℝ) * bigU Q₀ I ≤ bigU Q₀ I ^ 2 := by nlinarith
  nlinarith

theorem hclamp_holds (hQ : 10 ≤ Q₀) :
    I.1 * (rPar Q₀ I : ℝ) + errC Q₀ I + 2 ≤ 2 ^ pPar Q₀ I := by
  have hV := bigV_ge (Q₀ := Q₀) (I := I) hQ
  have hU := bigU_ge (Q₀ := Q₀) (I := I) hQ
  have hn := n_le_bigV (Q₀ := Q₀) (I := I)
  have hR := rPar_le_bigV (Q₀ := Q₀) (I := I)
  have hC := errC_le (Q₀ := Q₀) (I := I) hQ
  rw [two_pow_pPar]
  have h1 : (I.1 : ℝ) * rPar Q₀ I ≤ bigV Q₀ I ^ 3 := by
    calc (I.1 : ℝ) * rPar Q₀ I ≤ bigV Q₀ I * bigV Q₀ I ^ 2 :=
          mul_le_mul hn hR (by positivity) (by positivity)
      _ = bigV Q₀ I ^ 3 := by ring
  have h2 : bigV Q₀ I ^ 3 + 4 * bigV Q₀ I + 1 ≤ bigV Q₀ I ^ 4 := by
    have := bigV_cube (I := I) hQ
    have := bigV_le_cube (I := I) hQ
    linarith
  have h3 : bigV Q₀ I ^ 4 ≤ bigU Q₀ I ^ 4 :=
    pow_le_pow_left₀ (by positivity) bigV_le_bigU 4
  linarith

theorem hpR_holds (hQ : 10 ≤ Q₀) : 7 * I.1 * (rPar Q₀ I : ℝ) / 2 ^ pPar Q₀ I ≤ 1 / 2 := by
  have hV := bigV_ge (Q₀ := Q₀) (I := I) hQ
  have hU := bigU_ge (Q₀ := Q₀) (I := I) hQ
  have hn := n_le_bigV (Q₀ := Q₀) (I := I)
  have hR := rPar_le_bigV (Q₀ := Q₀) (I := I)
  rw [two_pow_pPar, div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : (I.1 : ℝ) * rPar Q₀ I ≤ bigV Q₀ I ^ 3 := by
    calc (I.1 : ℝ) * rPar Q₀ I ≤ bigV Q₀ I * bigV Q₀ I ^ 2 :=
          mul_le_mul hn hR (by positivity) (by positivity)
      _ = bigV Q₀ I ^ 3 := by ring
  have h3 : bigV Q₀ I ^ 4 ≤ bigU Q₀ I ^ 4 :=
    pow_le_pow_left₀ (by positivity) bigV_le_bigU 4
  have := bigV_cube (I := I) hQ
  have : 0 ≤ bigV Q₀ I ^ 3 := by positivity
  linarith

theorem ratio_nR_le : (ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I) ≤ 44 * (rPar Q₀ I : ℝ) ^ 2 := by
  have hr := ratioQ_le_z (I := I)
  have hr0 := ratioQ_nonneg (I := I)
  have hn : (I.1 : ℝ) ≤ zPar I := by exact_mod_cast (n_lt_zPar I).le
  have hZR := zPar_sq_le_rPar (Q₀ := Q₀) (I := I)
  have hR0 : (0 : ℝ) ≤ rPar Q₀ I := by positivity
  calc (ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I) ≤ (11 * zPar I) * (4 * zPar I * rPar Q₀ I) := by
        gcongr
    _ = 44 * ((zPar I : ℝ) ^ 2 * rPar Q₀ I) := by ring
    _ ≤ 44 * ((rPar Q₀ I : ℝ) * rPar Q₀ I) := by gcongr
    _ = 44 * (rPar Q₀ I : ℝ) ^ 2 := by ring

theorem hN_holds : 3 * ((ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I)) ^ 2 ≤ nSer Q₀ I := by
  have hr0 := ratioQ_nonneg (I := I)
  have hR0 : (0 : ℝ) ≤ rPar Q₀ I := by positivity
  have h1 := ratio_nR_le (Q₀ := Q₀) (I := I)
  have h0 : 0 ≤ (ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I) := by positivity
  have h2 : 3 * ((ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I)) ^ 2 ≤ 3 * (44 * (rPar Q₀ I : ℝ) ^ 2) ^ 2 :=
    by gcongr
  refine h2.trans ?_
  have h3 : (nSer Q₀ I : ℝ) = 30000 * ((rPar Q₀ I : ℝ) + 1) ^ 4 + tPar Q₀ I := by
    simp [nSer]
  rw [h3]
  have : (0 : ℝ) ≤ tPar Q₀ I := by positivity
  have h4 : (rPar Q₀ I : ℝ) ^ 4 ≤ ((rPar Q₀ I : ℝ) + 1) ^ 4 :=
    pow_le_pow_left₀ hR0 (by linarith) 4
  nlinarith

end Numbers

/-! ### The machine's signs are the ideal ones away from `0` -/

section Agree

variable {Q₀ : ℕ} {I : Instance}

/-- The accuracy of the projections, `2V⁴/U³`. -/
theorem abs_xiHat_sub_le (hI : Valid I) (hQ : 10 ≤ Q₀) (g : EuclideanSpace ℝ (Fin I.1))
    (hg : ∀ k, |g k| ≤ rPar Q₀ I) {k : ℕ} (hk : k < I.1) :
    |((xiHat Q₀ I (cellsE Q₀ I g)).getD k 0 : ℝ) - ⟪vAlg Q₀ I k, g⟫| ≤
      2 * bigV Q₀ I ^ 4 / bigU Q₀ I ^ 3 := by
  have hsmall := (errXi_le (I := I) hQ).trans ((errXi_le' hQ).trans
    (by norm_num : (1 : ℝ) / 8 ≤ 1))
  rw [getD_xiHat Q₀ I _ hk]
  refine (abs_xiNext_sub_le hI hQ g hg hsmall (hclamp_holds hQ) k hk).trans ?_
  refine le_trans ?_ (errXi_le hQ)
  have hE : 0 ≤ errE Q₀ I := by unfold errE; positivity
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀
    (by have := errC_nonneg (Q₀ := Q₀) (I := I); linarith) hk.le) hE

theorem tQ_nonneg : (0 : ℝ) ≤ tQ I := by
  have := kPar_pos I
  rw [tQ]; push_cast; positivity

theorem tQ_le_one : (tQ I : ℝ) ≤ 1 := by
  have : (5 : ℝ) ≤ kPar I := by exact_mod_cast five_le_kPar I
  rw [tQ]; push_cast
  rw [div_le_one (by positivity)]
  linarith

theorem le_quarter_div {a U : ℝ} {k : ℕ} (hU : 1 ≤ U) (h : 4 * a * U ≤ U ^ k) :
    a / U ^ k ≤ (1 / 4) / U := by
  have hU0 : 0 < U := by linarith
  rw [div_le_div_iff₀ (by positivity) hU0]
  linarith

theorem div_pow_le_quarter {a U : ℝ} {k : ℕ} (hU1 : 1 ≤ U) (h : 4 * a ≤ U ^ k) :
    a / U ^ (k + 1) ≤ (1 / 4) / U := by
  have hU0 : 0 < U := by linarith
  rw [div_le_div_iff₀ (by positivity) hU0, pow_succ]
  have := mul_le_mul_of_nonneg_right h hU0.le
  linarith

/-- The four error terms are each at most `1/(4U)` when `V ≥ 2^13` and `U ≥ V⁶`. -/
theorem small_terms_le {V U : ℝ} (hV : 8192 ≤ V) (hU : V ^ 6 ≤ U) :
    2 * V ^ 4 / U ^ 3 + 6 / U ^ 4 + (88 * V ^ 5 / U ^ 3 + 77 * V ^ 4 / U ^ 4) ≤ 1 / U := by
  have hV1 : 1 ≤ V := by linarith
  have hU1 : 1 ≤ U := (one_le_pow₀ hV1).trans hU
  have hV4 : 0 ≤ V ^ 4 := by positivity
  have hV5 : 8192 * V ^ 5 ≤ V ^ 6 := by
    rw [pow_succ V 5, mul_comm]; exact mul_le_mul_of_nonneg_left hV (by positivity)
  have hV45 : V ^ 4 ≤ V ^ 5 := pow_le_pow_right₀ hV1 (by norm_num)
  have hVV : V ≤ V ^ 6 := le_self_pow₀ hV1 (by norm_num)
  have hU2 : U ≤ U ^ 2 := le_self_pow₀ hU1 (by norm_num)
  have hU3 : U ≤ U ^ 3 := le_self_pow₀ hU1 (by norm_num)
  have a1 : 2 * V ^ 4 / U ^ 3 ≤ (1 / 4) / U :=
    div_pow_le_quarter (k := 2) hU1 (by linarith)
  have a2 : 6 / U ^ 4 ≤ (1 / 4) / U := div_pow_le_quarter (k := 3) hU1 (by linarith)
  have a3 : 88 * V ^ 5 / U ^ 3 ≤ (1 / 4) / U :=
    div_pow_le_quarter (k := 2) hU1 (by linarith)
  have a4 : 77 * V ^ 4 / U ^ 4 ≤ (1 / 4) / U :=
    div_pow_le_quarter (k := 3) hU1 (by linarith)
  have : (1 / 4) / U + (1 / 4) / U + ((1 / 4) / U + (1 / 4) / U) = 1 / U := by ring
  linarith

/-- The error of the votes, `B ≤ 6/U⁴ + 11 V (8V⁴/U³ + 7V³/U⁴)`. -/
theorem voteErr_le :
    2 * ((ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I) / 2 ^ nSer Q₀ I + 2 / 2 ^ tPar Q₀ I +
      (ratioQ I : ℝ) * (4 * (2 * bigV Q₀ I ^ 4 / bigU Q₀ I ^ 3) +
        7 * I.1 * rPar Q₀ I / 2 ^ pPar Q₀ I) / 2) ≤
      6 / bigU Q₀ I ^ 4 + 11 * bigV Q₀ I * (8 * bigV Q₀ I ^ 4 / bigU Q₀ I ^ 3 +
        7 * bigV Q₀ I ^ 3 / bigU Q₀ I ^ 4) := by
  obtain ⟨V, hVd⟩ : ∃ V, V = bigV Q₀ I := ⟨_, rfl⟩
  obtain ⟨U, hUd⟩ : ∃ U, U = bigU Q₀ I := ⟨_, rfl⟩
  rw [← hVd, ← hUd]
  have hT : (2 : ℝ) ^ pPar Q₀ I ≤ 2 ^ tPar Q₀ I :=
    pow_le_pow_right₀ (by norm_num) (by unfold tPar; omega)
  have hp : (2 : ℝ) ^ pPar Q₀ I = U ^ 4 := hUd ▸ two_pow_pPar
  have hR : (rPar Q₀ I : ℝ) ≤ V ^ 2 := hVd ▸ rPar_le_bigV
  have hn : (I.1 : ℝ) ≤ V := hVd ▸ n_le_bigV
  have hrat0 := ratioQ_nonneg (I := I)
  have hrat : (ratioQ I : ℝ) ≤ 11 * V :=
    (ratioQ_le_z (I := I)).trans (by have := zPar_le_bigV (Q₀ := Q₀) (I := I); rw [hVd]; linarith)
  have hR0 : (0 : ℝ) ≤ rPar Q₀ I := by positivity
  have hV0 : 0 ≤ V := by rw [hVd]; positivity
  have hU0 : 0 < U := by rw [hUd]; positivity
  have hnR : (I.1 : ℝ) * rPar Q₀ I ≤ V ^ 3 := by
    calc (I.1 : ℝ) * rPar Q₀ I ≤ V * V ^ 2 := mul_le_mul hn hR (by positivity) hV0
      _ = V ^ 3 := by ring
  -- `ratio · 4nR / 2^N ≤ 1/2^T`.
  have t1 : (ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I) / 2 ^ nSer Q₀ I ≤ 1 / 2 ^ tPar Q₀ I := by
    have hN2 : (2 : ℝ) ^ nSer Q₀ I = 2 ^ (30000 * (rPar Q₀ I + 1) ^ 4) * 2 ^ tPar Q₀ I := by
      rw [show nSer Q₀ I = 30000 * (rPar Q₀ I + 1) ^ 4 + tPar Q₀ I from rfl, pow_add]
    have hbig : (ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I) ≤ 2 ^ (30000 * (rPar Q₀ I + 1) ^ 4) := by
      have h3 := ratio_nR_le (Q₀ := Q₀) (I := I)
      have h5 := natCast_add_one_le_two_pow (30000 * (rPar Q₀ I + 1) ^ 4)
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h5
      have h6 : (rPar Q₀ I : ℝ) ^ 2 ≤ ((rPar Q₀ I : ℝ) + 1) ^ 4 := by
        have : (rPar Q₀ I : ℝ) ^ 2 ≤ ((rPar Q₀ I : ℝ) + 1) ^ 2 :=
          pow_le_pow_left₀ hR0 (by linarith) 2
        have h7 : ((rPar Q₀ I : ℝ) + 1) ^ 2 ≤ ((rPar Q₀ I : ℝ) + 1) ^ 4 :=
          pow_le_pow_right₀ (by linarith) (by norm_num)
        linarith
      have : (0 : ℝ) ≤ ((rPar Q₀ I : ℝ) + 1) ^ 4 := by positivity
      refine le_trans h3 (le_trans ?_ h5)
      linarith
    rw [hN2, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (ratioQ I : ℝ) * (4 * I.1 * rPar Q₀ I) * 2 ^ tPar Q₀ I
        ≤ 2 ^ (30000 * (rPar Q₀ I + 1) ^ 4) * 2 ^ tPar Q₀ I :=
          mul_le_mul_of_nonneg_right hbig (by positivity)
      _ = 1 * (2 ^ (30000 * (rPar Q₀ I + 1) ^ 4) * 2 ^ tPar Q₀ I) := (one_mul _).symm
  have t2 : (1 : ℝ) / 2 ^ tPar Q₀ I ≤ 1 / U ^ 4 := by
    rw [← hp]; exact one_div_le_one_div_of_le (by positivity) hT
  have t3 : 7 * I.1 * (rPar Q₀ I : ℝ) / 2 ^ pPar Q₀ I ≤ 7 * V ^ 3 / U ^ 4 := by
    rw [hp]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h2T : (2 : ℝ) / 2 ^ tPar Q₀ I ≤ 2 / U ^ 4 := by
    rw [show (2 : ℝ) / 2 ^ tPar Q₀ I = 2 * (1 / 2 ^ tPar Q₀ I) by ring,
      show (2 : ℝ) / U ^ 4 = 2 * (1 / U ^ 4) by ring]
    linarith
  have hin : 4 * (2 * V ^ 4 / U ^ 3) + 7 * I.1 * rPar Q₀ I / 2 ^ pPar Q₀ I ≤
      8 * V ^ 4 / U ^ 3 + 7 * V ^ 3 / U ^ 4 := by
    have : 4 * (2 * V ^ 4 / U ^ 3) = 8 * V ^ 4 / U ^ 3 := by ring
    linarith
  have hin0 : 0 ≤ 4 * (2 * V ^ 4 / U ^ 3) + 7 * I.1 * rPar Q₀ I / 2 ^ pPar Q₀ I := by
    positivity
  have hm := mul_le_mul hrat hin hin0 (by linarith)
  have e6 : (6 : ℝ) / U ^ 4 = 2 * (1 / U ^ 4) + 2 * (2 / U ^ 4) := by ring
  have e7 : (ratioQ I : ℝ) * (4 * (2 * V ^ 4 / U ^ 3) + 7 * I.1 * rPar Q₀ I / 2 ^ pPar Q₀ I) / 2 =
      (1 / 2) * ((ratioQ I : ℝ) *
        (4 * (2 * V ^ 4 / U ^ 3) + 7 * I.1 * rPar Q₀ I / 2 ^ pPar Q₀ I)) := by ring
  rw [e6, e7]
  linarith

/-- **The accuracy of the shifted arguments**: within `1/U` of `⟨vᵢ, g⟩ + λ fᵢ(g)`. -/
theorem abs_argL_sub_le (hI : Valid I) (hQ : 10 ≤ Q₀) (g : EuclideanSpace ℝ (Fin I.1))
    (hg : ∀ k, |g k| ≤ rPar Q₀ I) {i : ℕ} (hi : i < I.1) :
    |(((xiHat Q₀ I (cellsE Q₀ I g)).getD i 0 +
        tQ I * fHat Q₀ I (xiHat Q₀ I (cellsE Q₀ I g)) i : ℚ) : ℝ) -
      (⟪vAlg Q₀ I i, g⟫ + tQ I * fvote (vAlg Q₀ I) (windowSet (vAlg Q₀ I) I) (etaQ I) i g)| ≤
      1 / bigU Q₀ I := by
  obtain ⟨xi, hxi⟩ : ∃ xi, xi = xiHat Q₀ I (cellsE Q₀ I g) := ⟨_, rfl⟩
  rw [← hxi]
  have hξ : ∀ k < I.1, |(xi.getD k 0 : ℝ) - ⟪vAlg Q₀ I k, g⟫| ≤
      2 * bigV Q₀ I ^ 4 / bigU Q₀ I ^ 3 := fun k hk ↦ hxi ▸ abs_xiHat_sub_le hI hQ g hg hk
  have hε0 : 0 ≤ 2 * bigV Q₀ I ^ 4 / bigU Q₀ I ^ 3 := by positivity
  have hf := abs_fHat_sub_le hI hQ g hg xi hξ hε0 (errXi_le' hQ) (hpR_holds hQ) hN_holds i
  have hB := voteErr_le (Q₀ := Q₀) (I := I)
  have hsmall := small_terms_le (bigV_ge (I := I) hQ) (bigU_ge hQ)
  have e2 : 11 * bigV Q₀ I * (8 * bigV Q₀ I ^ 4 / bigU Q₀ I ^ 3 +
      7 * bigV Q₀ I ^ 3 / bigU Q₀ I ^ 4) =
      88 * bigV Q₀ I ^ 5 / bigU Q₀ I ^ 3 + 77 * bigV Q₀ I ^ 4 / bigU Q₀ I ^ 4 := by ring
  rw [e2] at hB
  have ht0 := tQ_nonneg (I := I)
  have ht1 := tQ_le_one (I := I)
  have e : (((xi.getD i 0 + tQ I * fHat Q₀ I xi i : ℚ)) : ℝ) -
      (⟪vAlg Q₀ I i, g⟫ + tQ I * fvote (vAlg Q₀ I) (windowSet (vAlg Q₀ I) I) (etaQ I) i g) =
      ((xi.getD i 0 : ℝ) - ⟪vAlg Q₀ I i, g⟫) + (tQ I : ℝ) * ((fHat Q₀ I xi i : ℝ) -
        fvote (vAlg Q₀ I) (windowSet (vAlg Q₀ I) I) (etaQ I) i g) := by
    push_cast; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg ht0]
  have h2 := mul_le_mul ht1 hf (abs_nonneg _) zero_le_one
  have h1 := hξ i hi
  linarith

/-- A sign is the same for two numbers closer than the size of one of them. -/
theorem decide_eq_of_abs_lt {x y δ : ℝ} (h : |x - y| ≤ δ) (hy : δ < |y|) :
    decide (0 ≤ x) = decide (0 ≤ y) := by
  rw [abs_le] at h
  rcases le_or_gt 0 y with hy0 | hy0
  · rw [abs_of_nonneg hy0] at hy
    simp only [decide_eq_decide]
    exact ⟨fun _ ↦ hy0, fun _ ↦ by linarith⟩
  · rw [abs_of_neg hy0] at hy
    simp only [decide_eq_decide]
    exact ⟨fun _ ↦ by linarith, fun h' ↦ absurd h' (not_le.2 hy0)⟩

theorem decide_ratCast (q : ℚ) : decide (0 ≤ q) = decide (0 ≤ (q : ℝ)) := by
  simp only [decide_eq_decide]
  exact ⟨fun h ↦ by exact_mod_cast h, fun h ↦ by exact_mod_cast h⟩

theorem getD_algC (cells : ℕ → ℕ) {i : ℕ} (hi : i < I.1) :
    (algC Q₀ I cells).getD i false =
      if branch0 Q₀ I then decide (0 ≤ (xiHat Q₀ I cells).getD i 0)
      else decide (0 ≤ (xiHat Q₀ I cells).getD i 0 +
        tQ I * fHat Q₀ I (xiHat Q₀ I cells) i) := by
  unfold algC
  split_ifs <;> simp [List.getD_eq_getElem?_getD, hi]

/-- **Hyperplane rounding is followed**: away from `⟨vᵢ, g⟩ = 0` the machine's sign is
`round0`. -/
theorem algC_eq_round0 (hI : Valid I) (hQ : 10 ≤ Q₀) (hb : branch0 Q₀ I = true)
    (g : EuclideanSpace ℝ (Fin I.1)) (hg : ∀ k, |g k| ≤ rPar Q₀ I) {i : ℕ} (hi : i < I.1)
    (hsep : 1 / bigU Q₀ I < |⟪vAlg Q₀ I i, g⟫|) :
    (algC Q₀ I (cellsE Q₀ I g)).getD i false = round0 (vAlg Q₀ I) g i := by
  rw [getD_algC _ hi, ite_eq_left hb, round0, decide_ratCast]
  refine decide_eq_of_abs_lt ((abs_xiHat_sub_le hI hQ g hg hi).trans ?_) hsep
  have hV := bigV_ge (Q₀ := Q₀) (I := I) hQ
  have hVU := bigU_ge (Q₀ := Q₀) (I := I) hQ
  have hU1 : 1 ≤ bigU Q₀ I := le_trans (one_le_pow₀ (by linarith)) hVU
  have hU2 : bigU Q₀ I ≤ bigU Q₀ I ^ 2 := le_self_pow₀ hU1 (by norm_num)
  have hU0 : 0 < bigU Q₀ I := by linarith
  rw [div_le_div_iff₀ (by positivity) hU0]
  have h4 : 2 * bigV Q₀ I ^ 4 ≤ bigV Q₀ I ^ 6 := by
    have : 2 * bigV Q₀ I ^ 4 ≤ bigV Q₀ I ^ 2 * bigV Q₀ I ^ 4 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    rw [← pow_add] at this
    exact this
  have h5 : 2 * bigV Q₀ I ^ 4 ≤ bigU Q₀ I ^ 2 := by linarith
  calc 2 * bigV Q₀ I ^ 4 * bigU Q₀ I ≤ bigU Q₀ I ^ 2 * bigU Q₀ I :=
        mul_le_mul_of_nonneg_right h5 hU0.le
    _ = 1 * bigU Q₀ I ^ 3 := by ring

/-- **The shifted rounding is followed**: away from `⟨vᵢ, g⟩ + λ fᵢ(g) = 0` the machine's sign is
`roundL`. -/
theorem algC_eq_roundL (hI : Valid I) (hQ : 10 ≤ Q₀) (hb : branch0 Q₀ I = false)
    (g : EuclideanSpace ℝ (Fin I.1)) (hg : ∀ k, |g k| ≤ rPar Q₀ I) {i : ℕ} (hi : i < I.1)
    (hsep : 1 / bigU Q₀ I <
      |⟪vAlg Q₀ I i, g⟫ + tQ I * fvote (vAlg Q₀ I) (windowSet (vAlg Q₀ I) I) (etaQ I) i g|) :
    (algC Q₀ I (cellsE Q₀ I g)).getD i false =
      roundL (vAlg Q₀ I) (windowSet (vAlg Q₀ I) I) (etaQ I) (tQ I) g i := by
  rw [getD_algC _ hi, ite_eq_right (by simp [hb]), roundL, decide_ratCast]
  exact decide_eq_of_abs_lt (abs_argL_sub_le hI hQ g hg hi) hsep

end Agree

end BGHKLMM26.Alg
