module

public import BMW26.SoS.FKN

/-!
# Theorem 4.1, as stated in `Challenge.lean`

`BMW26.sos_fkn_of_parts`, with `K = 200`. Both parts come from one construction,
`BMW26.fkn_cert`, which builds a proof from `fknSystem q` and tracks a property `Φ` of each of its
terms `p_S ∏_{i ∈ S} fᵢ` (`BMW26.DerivesNT`; `Φ` holds for `0` and is closed under sums and
constant multiples, `BMW26.TermClosed`). It starts from `BMW26.fkn`, which proves
`∑ᵢ f̂(i)⁴ - 1 + 10 (1 - ∑ᵢ f̂(i)²) ≥ 0` from the Boolean constraints alone, in the variables
`Cube d`, with multipliers of `‖·‖₁ ≤ 2^(40 (d + 4))` (`SoS.DerivesN`):

* take for the Boolean constraints the list `BMW26.boolSystem d`, and rename the variables
  `x ↦ some x` (`BMW26.DerivesNT.subst_X`: substituting variables for variables keeps the degree
  and does not increase `‖·‖₁`, and every term of the new proof is a renamed polynomial), which
  turns `aP {i}` into `fourierCoeff i` and `boolSystem d` into the tail of `fknSystem q`;
* move the proof to `fknSystem q`, which is that tail with two more constraints in front
  (`BMW26.DerivesNT.cons`, an instance of `BMW26.DerivesNT.of_injective`, which reindexes the
  multipliers along an injection of constraint indices; the terms are those of the old proof, and
  `0`);
* add `10 (∑ᵢ ⟨f, χᵢ⟩² - (1 - q))` and `190 q`, multiples of the first two constraints:
  `∑ ⟨f, χᵢ⟩⁴ - (1 - 200 q) = (∑ ⟨f, χᵢ⟩⁴ - 1 + 10 (1 - ∑ ⟨f, χᵢ⟩²)) + 10 (∑ ⟨f, χᵢ⟩² - (1 - q)) +
  190 q`;
* bound the coefficients (`BMW26.fkn_coeffs`): the multipliers have `‖·‖₁ ≤ 2^(40 (d + 4)) + 200`,
  and, since `‖⟨f, χᵢ⟩‖₁ = 1`, every coefficient of the constraints and of the goal is at most
  `d + 1 + 200 · 2^b` when those of `q` are at most `2^b`; both bounds are at most
  `2^(b + 200 (d + 1))`.

For the second part, `Φ` is trivial. For the first, `q = δ` and `Φ` is `BMW26.DeltaLinear`: every
monomial containing `δ` is `δ`. It holds for renamed polynomials (they do not contain `δ`), for
`∑ᵢ ⟨f, χᵢ⟩² - (1 - δ)` and for `δ`, which are the terms the construction produces.
-/

@[expose] public section

namespace BMW26

open MvPolynomial SoS

/-! ### Proofs with bounded multipliers and tracked terms -/

/-- A property of polynomials that holds for `0` and is closed under sums and constant
multiples. -/
structure TermClosed {σ : Type*} (Φ : MvPolynomial σ ℝ → Prop) : Prop where
  zero : Φ 0
  add : ∀ s t, Φ s → Φ t → Φ (s + t)
  C_mul : ∀ c t, Φ t → Φ (C c * t)

/-- A degree-`k` proof that `A` implies `g ≥ 0` whose multipliers have `‖·‖₁ ≤ M` and whose terms
`p_S ∏_{i ∈ S} fᵢ` all satisfy `Φ`. -/
def DerivesNT {σ : Type*} (A : System σ ℝ) (k : ℕ) (M : ℝ) (Φ : MvPolynomial σ ℝ → Prop)
    (g : MvPolynomial σ ℝ) : Prop :=
  ∃ P : Proof A g k, (∀ S, coeffNorm1 (P.mult S) ≤ M) ∧ ∀ S, Φ (P.mult S * A.prod S)

namespace DerivesNT

variable {σ : Type*} {A : System σ ℝ} {k : ℕ} {M M₁ M₂ : ℝ} {Φ : MvPolynomial σ ℝ → Prop}
  {g g' g₁ g₂ : MvPolynomial σ ℝ}

theorem congr (h : DerivesNT A k M Φ g) (e : g = g') : DerivesNT A k M Φ g' := e ▸ h

theorem add (hΦ : TermClosed Φ) (h₁ : DerivesNT A k M₁ Φ g₁) (h₂ : DerivesNT A k M₂ Φ g₂) :
    DerivesNT A k (M₁ + M₂) Φ (g₁ + g₂) := by
  obtain ⟨P₁, hM₁, hΦ₁⟩ := h₁
  obtain ⟨P₂, hM₂, hΦ₂⟩ := h₂
  refine ⟨P₁.add P₂, fun S ↦ (coeffNorm1_add_le _ _).trans (add_le_add (hM₁ S) (hM₂ S)),
    fun S ↦ ?_⟩
  change Φ ((P₁.mult S + P₂.mult S) * A.prod S)
  rw [add_mul]
  exact hΦ.add _ _ (hΦ₁ S) (hΦ₂ S)

theorem smul (hΦ : TermClosed Φ) {c : ℝ} (hc : 0 ≤ c) (h : DerivesNT A k M Φ g) :
    DerivesNT A k (c * M) Φ (C c * g) := by
  obtain ⟨P, hM, hP⟩ := h
  refine ⟨(P.mulSOS (IsSOS.const hc)).weaken (by simp), fun S ↦ ?_, fun S ↦ ?_⟩
  · change coeffNorm1 (C c * P.mult S) ≤ c * M
    rw [coeffNorm1_C_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (hM S) hc
  · change Φ (C c * P.mult S * A.prod S)
    rw [mul_assoc]
    exact hΦ.C_mul c _ (hP S)

/-- A constraint `f = fᵢ` of `A` proves itself, with the single term `fᵢ`. -/
theorem of_get (hΦ : TermClosed Φ) (i : Fin A.length) {f : MvPolynomial σ ℝ} (hi : A.get i = f)
    (hdeg : f.totalDegree ≤ k) (hf : Φ f) : DerivesNT A k 1 Φ f := by
  subst hi
  refine ⟨Proof.assumption A i hdeg, fun S ↦ ?_, fun S ↦ ?_⟩
  · by_cases h : S = {i}
    · simp [Proof.assumption, h, coeffNorm1_one]
    · simp [Proof.assumption, h, coeffNorm1]
  · by_cases h : S = {i}
    · subst h
      simpa [Proof.assumption, System.prod] using hf
    · simpa [Proof.assumption, h] using hΦ.zero

/-- A proof from `A` is a proof from `B`, with the same multipliers and terms, when the
constraints of `A` are, with their indices, among those of `B`: the multiplier of a set `T` of
constraints of `B` is that of the set `S` of constraints of `A` that `ι` maps onto `T`, if there is
one, and `0` otherwise. -/
theorem of_injective {B : System σ ℝ} (hΦ : TermClosed Φ) (h : DerivesNT A k M Φ g)
    (ι : Fin A.length → Fin B.length) (hι : Function.Injective ι)
    (hget : ∀ i, B.get (ι i) = A.get i) : DerivesNT B k M Φ g := by
  classical
  obtain ⟨P, hP, hPΦ⟩ := h
  have hM : 0 ≤ M := (coeffNorm1_nonneg _).trans (hP ∅)
  let e : Fin A.length ↪ Fin B.length := ⟨ι, hι⟩
  have hprod : ∀ S, B.prod (S.map e) = A.prod S := fun S ↦ by
    unfold System.prod
    rw [Finset.prod_map]
    exact Finset.prod_congr rfl fun i _ ↦ hget i
  have hdeg : ∀ S, B.degree (S.map e) = A.degree S := fun S ↦ by
    unfold System.degree
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← hget i]; rfl
  have hfib : ∀ S, (Finset.univ.filter fun S' : Finset (Fin A.length) ↦ S'.map e = S.map e) =
      {S} := fun S ↦ by
    ext S'
    simp [Finset.map_inj]
  -- The multiplier of `T`, and its two cases.
  set mult : Finset (Fin B.length) → MvPolynomial σ ℝ := fun T ↦
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin A.length) ↦ S.map e = T), P.mult S with hmult
  have hmap : ∀ S, mult (S.map e) = P.mult S := fun S ↦ by
    rw [hmult]
    dsimp only
    rw [hfib, Finset.sum_singleton]
  have hnot : ∀ T, (∀ S : Finset (Fin A.length), S.map e ≠ T) → mult T = 0 := fun T hT ↦
    Finset.sum_eq_zero fun S hS ↦ absurd (Finset.mem_filter.1 hS).2 (hT S)
  refine ⟨{ mult := mult
            isSOS_mult := fun T ↦ IsSOS.sum _ fun S _ ↦ P.isSOS_mult S
            degree_le := fun T hT ↦ ?_
            eq_sum := ?_ }, fun T ↦ ?_, fun T ↦ ?_⟩
  · by_cases hS : ∃ S : Finset (Fin A.length), S.map e = T
    · obtain ⟨S, rfl⟩ := hS
      rw [hmap] at hT ⊢
      rw [hdeg]
      exact P.degree_le S hT
    · push Not at hS
      exact absurd (hnot T hS) hT
  · refine P.eq_sum.trans ?_
    rw [hmult]
    simp_rw [Finset.sum_mul]
    have : ∀ T, ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin A.length) ↦ S.map e = T),
        P.mult S * B.prod T =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin A.length) ↦ S.map e = T),
          P.mult S * A.prod S := fun T ↦
      Finset.sum_congr rfl fun S hS ↦ by rw [← (Finset.mem_filter.1 hS).2, hprod]
    rw [Finset.sum_congr rfl fun T _ ↦ this T]
    exact (Finset.sum_fiberwise _ (fun S : Finset (Fin A.length) ↦ S.map e) _).symm
  · by_cases hS : ∃ S : Finset (Fin A.length), S.map e = T
    · obtain ⟨S, rfl⟩ := hS
      dsimp only
      rw [hmap]
      exact hP S
    · push Not at hS
      dsimp only
      rw [hnot T hS]
      simpa [coeffNorm1] using hM
  · by_cases hS : ∃ S : Finset (Fin A.length), S.map e = T
    · obtain ⟨S, rfl⟩ := hS
      dsimp only
      rw [hmap, hprod]
      exact hPΦ S
    · push Not at hS
      dsimp only
      rw [hnot T hS, zero_mul]
      exact hΦ.zero

/-- A proof from `A` is a proof from `f :: A`, with the same multipliers and terms. -/
theorem cons (hΦ : TermClosed Φ) (h : DerivesNT A k M Φ g) (f : MvPolynomial σ ℝ) :
    DerivesNT (f :: A) k M Φ g :=
  of_injective hΦ h Fin.succ (Fin.succ_injective _) fun _ ↦ rfl

/-- Forgetting the terms. -/
theorem derivesN (h : DerivesNT A k M Φ g) : DerivesN A k M g := by
  obtain ⟨P, hP, -⟩ := h
  exact ⟨P, hP⟩

/-- Bounds on the multipliers, the constraints and the goal bound the coefficients of the proof. -/
theorem bitComplexityLE {B : ℝ} (h : DerivesNT A k M Φ g) (hM : M ≤ 2 ^ B)
    (hA : ∀ f ∈ A, CoeffsLE f (2 ^ B)) (hg : CoeffsLE g (2 ^ B)) :
    ∃ P : Proof A g k, P.BitComplexityLE B ∧ ∀ S, Φ (P.mult S * A.prod S) := by
  obtain ⟨P, hP, hPΦ⟩ := h
  refine ⟨P, ⟨hA, hg, fun S m ↦ ?_⟩, hPΦ⟩
  simpa using (abs_coeff_le_coeffNorm1 (P.mult S) m).trans ((hP S).trans hM)

end DerivesNT

/-! ### Renaming variables -/

theorem aeval_X_eq_rename {σ τ : Type*} (f : σ → τ) (p : MvPolynomial σ ℝ) :
    aeval (fun x ↦ (X (f x) : MvPolynomial τ ℝ)) p = rename f p := by
  rw [← aeval_X_left_apply (rename f p), aeval_rename]
  rfl

/-- Substituting variables for variables does not increase `‖·‖₁`. -/
theorem coeffNorm1_aeval_X_le {σ τ : Type*} (f : σ → τ) (p : MvPolynomial σ ℝ) :
    coeffNorm1 (aeval (fun x ↦ (X (f x) : MvPolynomial τ ℝ)) p) ≤ coeffNorm1 p := by
  rw [aeval_X_eq_rename]
  conv_lhs => rw [p.as_sum, map_sum]
  refine (coeffNorm1_sum_le _ _).trans (le_of_eq ?_)
  change _ = ∑ m ∈ p.support, |p.coeff m|
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [rename_monomial, coeffNorm1_monomial]

/-- A product of substituted constraints is a substituted polynomial. -/
theorem prod_map_aeval {σ τ : Type*} (A : System σ ℝ) (φ : σ → MvPolynomial τ ℝ)
    (S : Finset (Fin (A.map (aeval φ)).length)) :
    ∃ r : MvPolynomial σ ℝ, System.prod (A.map (aeval φ)) S = aeval φ r := by
  refine ⟨∏ i ∈ S, A.get (Fin.cast (by simp) i), ?_⟩
  change ∏ i ∈ S, (A.map (aeval φ)).get i = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp [List.get_eq_getElem]

/-- Substituting variables for variables in a proof keeps its degree and the bound on its
multipliers; its terms become substituted polynomials. -/
theorem DerivesNT.subst_X {σ τ : Type*} {A : System σ ℝ} {k : ℕ} {M : ℝ}
    {g : MvPolynomial σ ℝ} (h : DerivesN A k M g) (f : σ → τ) {Φ : MvPolynomial τ ℝ → Prop}
    (hren : ∀ p : MvPolynomial σ ℝ, Φ (aeval (fun x ↦ (X (f x) : MvPolynomial τ ℝ)) p)) :
    DerivesNT (A.map (aeval fun x ↦ (X (f x) : MvPolynomial τ ℝ))) k M Φ
      (aeval (fun x ↦ (X (f x) : MvPolynomial τ ℝ)) g) := by
  obtain ⟨P, hP⟩ := h
  have hφ : ∀ x, (X (f x) : MvPolynomial τ ℝ).totalDegree ≤ 1 := fun x ↦ (totalDegree_X _).le
  have h1 : DerivesNT (A.map (aeval fun x ↦ (X (f x) : MvPolynomial τ ℝ))) (k * 1) M Φ
      (aeval (fun x ↦ (X (f x) : MvPolynomial τ ℝ)) g) := by
    refine ⟨P.subst (fun x ↦ (X (f x) : MvPolynomial τ ℝ)) hφ, fun S ↦
      (coeffNorm1_aeval_X_le f _).trans (hP _), fun S ↦ ?_⟩
    obtain ⟨p, hp⟩ : ∃ p, (P.subst (fun x ↦ (X (f x) : MvPolynomial τ ℝ)) hφ).mult S =
        aeval (fun x ↦ (X (f x) : MvPolynomial τ ℝ)) p := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ := prod_map_aeval A (fun x ↦ (X (f x) : MvPolynomial τ ℝ)) S
    rw [hp, hr, ← map_mul]
    exact hren _
  rwa [mul_one] at h1

/-! ### Coefficient bounds -/

theorem coeffsLE_of_coeffNorm1 {σ : Type*} {p : MvPolynomial σ ℝ} {a : ℝ}
    (h : coeffNorm1 p ≤ a) : CoeffsLE p a := fun m ↦ by
  simpa using (abs_coeff_le_coeffNorm1 p m).trans h

theorem coeffsLE_mono {σ : Type*} {p : MvPolynomial σ ℝ} {a a' : ℝ} (h : CoeffsLE p a)
    (ha : a ≤ a') : CoeffsLE p a' := fun m ↦ (h m).trans ha

/-- The coefficients of `r + c q` are at most `‖r‖₁ + |c| b` when those of `q` are at most `b`. -/
theorem coeffsLE_add_C_mul {σ : Type*} {r q : MvPolynomial σ ℝ} {a b : ℝ} (c : ℝ)
    (hr : coeffNorm1 r ≤ a) (hq : CoeffsLE q b) : CoeffsLE (r + C c * q) (a + |c| * b) :=
  fun m ↦ by
  have h := hq m
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h ⊢
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul]
  refine (abs_add_le _ _).trans (add_le_add ((abs_coeff_le_coeffNorm1 r m).trans hr) ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg c)

/-! ### The polynomials of Theorem 4.1 -/

/-- The Boolean constraints `X x² - 1 ≥ 0` and `1 - X x² ≥ 0` in the variables `Cube d`. -/
noncomputable def boolSystem (d : ℕ) : System (Cube d) ℝ :=
  Finset.univ.toList.flatMap fun x : Cube d ↦ [X x ^ 2 - 1, 1 - X x ^ 2]

theorem aeval_aP {d : ℕ} (i : Fin d) :
    aeval (fun x : Cube d ↦ (X (some x) : MvPolynomial (FKNVar d) ℝ)) (aP {i}) =
      fourierCoeff i := by
  simp [aP, fcP, fourierCoeff, chi_singleton, MvPolynomial.algebraMap_eq]

theorem totalDegree_fourierCoeff {d : ℕ} (i : Fin d) : (fourierCoeff i).totalDegree ≤ 1 :=
  FKN.deg_C_mul _ (FKN.deg_sum _ fun _ _ ↦ FKN.deg_C_mul _ (totalDegree_X _).le)

theorem coeffNorm1_fourierCoeff {d : ℕ} (i : Fin d) : coeffNorm1 (fourierCoeff i) ≤ 1 := by
  rw [← aeval_aP]
  exact (coeffNorm1_aeval_X_le some _).trans (FKN.nm_aP {i})

/-- `‖∑ᵢ ⟨f, χᵢ⟩ʲ - 1‖₁ ≤ d + 1`. -/
theorem coeffNorm1_sum_fourierCoeff_pow_sub_one {d : ℕ} (j : ℕ) :
    coeffNorm1 (∑ i, fourierCoeff i ^ j - 1 : MvPolynomial (FKNVar d) ℝ) ≤ d + 1 := by
  have h : coeffNorm1 (∑ i, fourierCoeff i ^ j - 1 : MvPolynomial (FKNVar d) ℝ) ≤
      (Finset.univ : Finset (Fin d)).card * 1 + 1 := FKN.nm_sub (FKN.nm_sum Finset.univ fun i _ ↦
    ((coeffNorm1_pow_le (fourierCoeff i) j).trans
      (pow_le_one₀ (coeffNorm1_nonneg _) (coeffNorm1_fourierCoeff i)))) coeffNorm1_one.le
  simpa using h

/-! ### The certificate -/

/-- **The certificate** of Theorem 4.1 from `fknSystem q`, with `K = 200`, multipliers of
`‖·‖₁ ≤ 2^(40 (d + 4)) + 200`, and terms satisfying `Φ`, for any `Φ` closed under sums and constant
multiples that holds for renamed polynomials and for the first two constraints. -/
theorem fkn_cert {d : ℕ} (q : MvPolynomial (FKNVar d) ℝ) (hq : q.totalDegree ≤ 2)
    {Φ : MvPolynomial (FKNVar d) ℝ → Prop} (hΦ : TermClosed Φ)
    (hren : ∀ p : MvPolynomial (Cube d) ℝ,
      Φ (aeval (fun x : Cube d ↦ (X (some x) : MvPolynomial (FKNVar d) ℝ)) p))
    (h₁ : Φ (∑ i, fourierCoeff i ^ 2 - (1 - q))) (h₂ : Φ q) :
    DerivesNT (fknSystem q) 4 (2 ^ (40 * (d + 4)) + 10 * 1 + 190 * 1) Φ
      (∑ i, fourierCoeff i ^ 4 - (1 - C 200 * q)) := by
  -- `fkn` from the Boolean constraints over `Cube d`.
  have hbool : ∀ x, X x ^ 2 - 1 ∈ boolSystem d ∧ 1 - X x ^ 2 ∈ boolSystem d := fun x ↦
    ⟨List.mem_flatMap.2 ⟨x, by simp, by simp⟩, List.mem_flatMap.2 ⟨x, by simp, by simp⟩⟩
  -- Rename `x ↦ some x`.
  have h1 := DerivesNT.subst_X (fkn (boolSystem d) hbool) some hren
  have hsys : (boolSystem d).map
      (aeval fun x : Cube d ↦ (X (some x) : MvPolynomial (FKNVar d) ℝ)) =
      Finset.univ.toList.flatMap fun x : Cube d ↦ [X (some x) ^ 2 - 1, 1 - X (some x) ^ 2] := by
    simp [boolSystem, List.map_flatMap]
  rw [hsys] at h1
  simp only [map_add, map_sub, map_sum, map_pow, map_mul, map_one, map_ofNat, aeval_aP] at h1
  -- The larger system.
  have h2 := DerivesNT.cons hΦ (DerivesNT.cons hΦ h1 q) (∑ i, fourierCoeff i ^ 2 - (1 - q))
  -- Ten times the first constraint, and `190` times the second.
  have hdeg : (∑ i, fourierCoeff i ^ 2 - (1 - q)).totalDegree ≤ 4 :=
    (FKN.deg_sub (FKN.deg_sum _ fun i _ ↦ (FKN.deg_sq (totalDegree_fourierCoeff i)).trans
      (by norm_num)) (FKN.deg_sub FKN.deg_one (hq.trans (by norm_num))))
  have h3 := DerivesNT.smul hΦ (by norm_num : (0 : ℝ) ≤ 10)
    (DerivesNT.of_get hΦ (A := fknSystem q) ⟨0, by simp [fknSystem]⟩
      (f := ∑ i, fourierCoeff i ^ 2 - (1 - q)) rfl hdeg h₁)
  have h4 := DerivesNT.smul hΦ (by norm_num : (0 : ℝ) ≤ 190)
    (DerivesNT.of_get hΦ (A := fknSystem q) (k := 4) ⟨1, by simp [fknSystem]⟩ (f := q) rfl
      (hq.trans (by norm_num)) h₂)
  have h5 := DerivesNT.add hΦ (DerivesNT.add hΦ h2 h3) h4
  refine DerivesNT.congr h5 ?_
  rw [show (C 10 : MvPolynomial (FKNVar d) ℝ) = 10 from map_ofNat C 10,
    show (C 190 : MvPolynomial (FKNVar d) ℝ) = 190 from map_ofNat C 190,
    show (C 200 : MvPolynomial (FKNVar d) ℝ) = 200 from map_ofNat C 200]
  ring

/-- The numbers of the coefficient bound: with `B = b + 200 (d + 1)`, both the bound on the
multipliers and the bound on the coefficients are at most `2^B`. -/
theorem fkn_bits_le (d b : ℕ) :
    (2 : ℝ) ^ (40 * (d + 4)) + 10 * 1 + 190 * 1 ≤ 2 ^ ((b : ℝ) + 200 * ((d : ℝ) + 1)) ∧
      (d : ℝ) + 1 + |200| * 2 ^ b ≤ 2 ^ ((b : ℝ) + 200 * ((d : ℝ) + 1)) := by
  have hB : (2 : ℝ) ^ ((b : ℝ) + 200 * ((d : ℝ) + 1)) = 2 ^ b * 2 ^ (200 * (d + 1)) := by
    rw [show (b : ℝ) + 200 * ((d : ℝ) + 1) = ((b + 200 * (d + 1) : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_add]
  have hb : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have hsplit : (2 : ℝ) ^ (200 * (d + 1)) = 2 ^ (40 * (d + 4)) * 2 ^ (160 * d + 40) := by
    rw [← pow_add]
    congr 1
    ring
  have ht : (256 : ℝ) ≤ 2 ^ (40 * (d + 4)) :=
    le_trans (by norm_num) (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 8 ≤ _))
  have hu : (2 : ℝ) ≤ 2 ^ (160 * d + 40) :=
    le_trans (by norm_num) (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ _))
  have hd : (d : ℝ) + 201 ≤ 2 ^ (200 * (d + 1)) := by
    have : d + 201 ≤ 2 ^ (200 * (d + 1)) := by
      have := Nat.lt_two_pow_self (n := 200 * (d + 1))
      omega
    exact_mod_cast this
  rw [hB]
  have hT : (0 : ℝ) ≤ 2 ^ (200 * (d + 1)) := by positivity
  constructor
  · rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 2 ^ (40 * (d + 4))),
      mul_le_mul_of_nonneg_right hb
        (by positivity : (0 : ℝ) ≤ 2 ^ (40 * (d + 4)) * 2 ^ (160 * d + 40))]
  · rw [abs_of_pos (by norm_num : (0 : ℝ) < 200)]
    nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2 ^ b),
      mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

/-- The coefficients of the constraints and of the goal are at most `2^(b + 200 (d + 1))` when
those of `q` are at most `2^b`. -/
theorem fkn_coeffs {d : ℕ} (b : ℕ) (q : MvPolynomial (FKNVar d) ℝ) (hqb : CoeffsLE q (2 ^ b)) :
    (∀ f ∈ fknSystem q, CoeffsLE f (2 ^ ((b : ℝ) + 200 * ((d : ℝ) + 1)))) ∧
      CoeffsLE (∑ i, fourierCoeff i ^ 4 - (1 - C 200 * q))
        (2 ^ ((b : ℝ) + 200 * ((d : ℝ) + 1))) := by
  obtain ⟨-, hcoef⟩ := fkn_bits_le d b
  have h2b : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h200 : |(200 : ℝ)| = 200 := abs_of_pos (by norm_num)
  refine ⟨fun f hf ↦ ?_, ?_⟩
  · simp only [fknSystem, List.mem_cons, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ,
      true_and, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | ⟨x, rfl | rfl⟩
    · have h := coeffsLE_add_C_mul 1 (coeffNorm1_sum_fourierCoeff_pow_sub_one (d := d) 2) hqb
      have e1 : ∑ i, fourierCoeff i ^ 2 - 1 + C 1 * q = ∑ i, fourierCoeff i ^ 2 - (1 - q) := by
        rw [C_1]
        ring
      rw [e1] at h
      refine coeffsLE_mono h (le_trans ?_ hcoef)
      rw [abs_one, h200]
      linarith
    · refine coeffsLE_mono hqb (le_trans ?_ hcoef)
      rw [h200]
      linarith
    · refine coeffsLE_of_coeffNorm1 ((FKN.nm_sub (FKN.nm_sq (coeffNorm1_X _).le)
        coeffNorm1_one.le).trans (le_trans ?_ hcoef))
      rw [h200]
      linarith
    · refine coeffsLE_of_coeffNorm1 ((FKN.nm_sub coeffNorm1_one.le
        (FKN.nm_sq (coeffNorm1_X _).le)).trans (le_trans ?_ hcoef))
      rw [h200]
      linarith
  · have h := coeffsLE_add_C_mul 200 (coeffNorm1_sum_fourierCoeff_pow_sub_one (d := d) 4) hqb
    have e1 : ∑ i, fourierCoeff i ^ 4 - 1 + C 200 * q =
        ∑ i, fourierCoeff i ^ 4 - (1 - C 200 * q) := by
      ring
    rw [e1] at h
    exact coeffsLE_mono h hcoef

/-! ### `δ` only as the monomial `δ` -/

/-- Every monomial of `t` that contains `δ` is `δ`. -/
def DeltaLinear {d : ℕ} (t : MvPolynomial (FKNVar d) ℝ) : Prop :=
  ∀ m ∈ t.support, m none ≠ 0 → m = Finsupp.single none 1

theorem deltaLinear_closed {d : ℕ} : TermClosed (DeltaLinear (d := d)) where
  zero m hm := by simp at hm
  add s t hs ht m hm := by
    rcases Finset.mem_union.1 (support_add hm) with h | h
    exacts [hs m h, ht m h]
  C_mul c t ht m hm := ht m (by rw [C_mul'] at hm; exact support_smul hm)

/-- Renamed polynomials do not contain `δ`. -/
theorem deltaLinear_aeval_some {d : ℕ} (p : MvPolynomial (Cube d) ℝ) :
    DeltaLinear (aeval (fun x : Cube d ↦ (X (some x) : MvPolynomial (FKNVar d) ℝ)) p) := by
  classical
  intro m hm hm0
  rw [aeval_X_eq_rename] at hm
  have hv : none ∈ (rename some p).vars :=
    (mem_vars_iff_mem_support none).2 ⟨m, hm, Finsupp.mem_support_iff.2 hm0⟩
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (vars_rename some p hv)
  exact absurd hx (Option.some_ne_none x)

theorem deltaLinear_X_none {d : ℕ} : DeltaLinear (X none : MvPolynomial (FKNVar d) ℝ) := by
  intro m hm _
  rw [support_X] at hm
  exact Finset.mem_singleton.1 hm

/-- **[BMW26, Theorem 4.1]**, the statement of `Challenge.lean`. -/
theorem sos_fkn_of_parts :
    ∃ K : ℝ,
      (∀ d : ℕ, ∃ P : Proof (fknSystem (X none : MvPolynomial (FKNVar d) ℝ))
          (∑ i, fourierCoeff i ^ 4 - (1 - C K * X none)) 4,
        P.BitComplexityLE (K * (d + 1)) ∧
          ∀ S, ∀ m ∈ (P.mult S * System.prod (fknSystem (X none : MvPolynomial (FKNVar d) ℝ))
            S).support, m none ≠ 0 → m = Finsupp.single none 1) ∧
      ∀ (d b : ℕ) (q : MvPolynomial (FKNVar d) ℝ), q.totalDegree ≤ 2 →
        CoeffsLE q (2 ^ b) →
          DerivesWithin (fknSystem q) 4 (b + K * (d + 1))
            (∑ i, fourierCoeff i ^ 4 - (1 - C K * q)) := by
  refine ⟨200, fun d ↦ ?_, fun d b q hq hqb ↦ ?_⟩
  · -- The paper's system, `q = δ`, with the terms tracked.
    have hδ : (X none : MvPolynomial (FKNVar d) ℝ).totalDegree ≤ 2 := by
      rw [totalDegree_X]
      norm_num
    have h₁ : DeltaLinear (∑ i, fourierCoeff i ^ 2 - (1 - X none) :
        MvPolynomial (FKNVar d) ℝ) := by
      have e : (∑ i, fourierCoeff i ^ 2 - (1 - X none) : MvPolynomial (FKNVar d) ℝ) =
          aeval (fun x : Cube d ↦ (X (some x) : MvPolynomial (FKNVar d) ℝ))
            (∑ i, aP {i} ^ 2 - 1) + X none := by
        simp only [map_sub, map_sum, map_pow, map_one, aeval_aP]
        ring
      rw [e]
      exact deltaLinear_closed.add _ _ (deltaLinear_aeval_some _) deltaLinear_X_none
    have hcert := fkn_cert (X none) hδ deltaLinear_closed deltaLinear_aeval_some h₁
      deltaLinear_X_none
    have hδb : CoeffsLE (X none : MvPolynomial (FKNVar d) ℝ) (2 ^ 0) :=
      coeffsLE_of_coeffNorm1 (by rw [coeffNorm1_X]; norm_num)
    obtain ⟨hA, hg⟩ := fkn_coeffs 0 (X none) hδb
    obtain ⟨hM, -⟩ := fkn_bits_le d 0
    rw [Nat.cast_zero, zero_add] at hA hg hM
    exact hcert.bitComplexityLE hM hA hg
  · -- Any `q`, with nothing tracked.
    have hcert := fkn_cert q hq (Φ := fun _ ↦ True)
      ⟨trivial, fun _ _ _ _ ↦ trivial, fun _ _ _ ↦ trivial⟩ (fun _ ↦ trivial) trivial trivial
    obtain ⟨hA, hg⟩ := fkn_coeffs b q hqb
    obtain ⟨P, hP, -⟩ := hcert.bitComplexityLE (fkn_bits_le d b).1 hA hg
    exact ⟨P, hP⟩

end BMW26
