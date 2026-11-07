module

public import Background.SumOfSquares.GridMoments

/-!
# The convex set the algorithm optimizes over

The sum-of-squares algorithm, stated mathematically: the set it searches with the ellipsoid
method, why every competitor lies deep inside it, and how its answer becomes a pseudo-expectation.

**Coordinates** (`SoS.Lifted.Coord`). A point lists the moments `y_m` of the monomials of degree
`1` to `ℓ` (the moment of `1` is fixed to `1`; `SoS.Lifted.ys`), and for each set `S` of
constraints in `SoS.Lifted.sets` (nonempty, nonconstant, of degree at most `ℓ`) an auxiliary
sequence `w_S` of degree `ℓ - deg S` (`SoS.Lifted.ws`).

**The set** (`SoS.Lifted.InSet A ℓ η τ R`): the moment matrices of `y` and of every `w_S` are at
least `-τ` (`SoS.MinEigGE`); the localized moments `L_y (xᵐ ∏ i ∈ S, fᵢ)` are within Euclidean
distance `η ∏ i ∈ S, ‖fᵢ‖₂` of `w_S`; every coordinate is at most `R`. With `τ = 0` this is the
semidefinite description of `η`-approximate satisfaction
(`SoS.PseudoExpectation.approxSatisfies_iff`).
The algorithm checks membership exactly, with rational arithmetic.

**The objective** (`SoS.Lifted.obj`): `L_y q₀ + ∑ⱼ (L_y qⱼ)²`, a convex function of `y`.

**The argument.**
* Every competitor, a pseudo-expectation that satisfies the constraints `η`-approximately with
  bounded moments, gives a point of `InSet A ℓ η 0 R₀` (`SoS.Lifted.exists_lift`).
* Every point within `ρ` of such a point, coordinate by coordinate, is in the relaxed set
  `InSet A ℓ (η + γ') τ R`, for explicit small `ρ` (`SoS.Lifted.mem_of_near`), and its objective
  is close (`SoS.Lifted.abs_obj_sub_le`). So the relaxed set contains a ball around every
  competitor, and the ellipsoid method finds a point of it whose objective is nearly as small as
  every competitor's (`Ellipsoid.exists_feasible_le`).
* That point's moment matrices are only approximately positive semidefinite. Mixing it with the
  grid moments (`SoS.Lifted.mix`) makes them exactly positive semidefinite, and the result
  satisfies the constraints `(η + γ)`-approximately (`SoS.Lifted.output`), with almost the same
  objective (`SoS.Lifted.abs_obj_mix_sub_le`).
-/

@[expose] public section

namespace SoS.Lifted

open MvPolynomial
open scoped RealInnerProductSpace

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K] [Algebra K ℝ]

/-! ### The coordinates -/

open Classical in
/-- The sets of constraints that get an auxiliary moment sequence: nonempty sets of nonconstant
constraints, of degree at most `ℓ`. -/
noncomputable def sets (A : System σ K) (ℓ : ℕ) : Finset (Finset (Fin A.length)) :=
  Finset.univ.filter fun S ↦ S.Nonempty ∧ (∀ i ∈ S, (A.get i).totalDegree ≠ 0) ∧ A.degree S ≤ ℓ

omit [Fintype σ] [DecidableEq σ] [Algebra K ℝ] in
theorem degree_le_of_mem_sets {A : System σ K} {ℓ : ℕ} {S : Finset (Fin A.length)}
    (hS : S ∈ sets A ℓ) : A.degree S ≤ ℓ := by
  classical
  unfold sets at hS
  exact (Finset.mem_filter.1 hS).2.2.2

/-- The coordinates: the moments of the monomials of degree `1` to `ℓ`, and for each set `S` of
constraints, the auxiliary moments of degree at most `ℓ - deg S`. -/
abbrev Coord (A : System σ K) (ℓ : ℕ) : Type _ :=
  (monomialsLE σ ℓ).erase 0 ⊕ (S : sets A ℓ) × monomialsLE σ (ℓ - A.degree S.1)

variable {A : System σ K} {ℓ : ℕ}

/-- The moments of a point: its coordinates, `1` at the monomial `1`, and `0` beyond degree
`ℓ`. -/
noncomputable def ys (x : Coord A ℓ → ℝ) : (σ →₀ ℕ) → ℝ := fun m ↦
  if h : m ∈ (monomialsLE σ ℓ).erase 0 then x (.inl ⟨m, h⟩) else if m = 0 then 1 else 0

/-- The auxiliary moments of a point for the set `S`, and `0` beyond degree `ℓ - deg S`. -/
noncomputable def ws (x : Coord A ℓ → ℝ) (S : sets A ℓ) : (σ →₀ ℕ) → ℝ := fun m ↦
  if h : m ∈ monomialsLE σ (ℓ - A.degree S.1) then x (.inr ⟨S, ⟨m, h⟩⟩) else 0

omit [Algebra K ℝ] in
@[simp] theorem ys_zero (x : Coord A ℓ → ℝ) : ys x 0 = 1 := by
  simp [ys]

/-- The localized moments `L_y (xᵐ ∏ i ∈ S, fᵢ)`. -/
noncomputable def loc (A : System σ K) (y : (σ →₀ ℕ) → ℝ) (S : Finset (Fin A.length))
    (m : σ →₀ ℕ) : ℝ :=
  riesz y (monomial m 1 * toReal (A.prod S))

omit [Fintype σ] [DecidableEq σ] in
/-- The polynomial `xᵐ ∏ i ∈ S, fᵢ` has degree at most `ℓ` when `deg m ≤ ℓ - deg S`. -/
theorem totalDegree_monomial_mul_prod_le {S : Finset (Fin A.length)} (hS : A.degree S ≤ ℓ)
    {m : σ →₀ ℕ} (hm : m.degree ≤ ℓ - A.degree S) :
    (monomial m (1 : ℝ) * toReal (A.prod S)).totalDegree ≤ ℓ := by
  have h1 := totalDegree_mul (monomial m (1 : ℝ)) (toReal (A.prod S))
  have h2 := (totalDegree_toReal_le (A.prod S)).trans (A.totalDegree_prod_le S)
  rw [totalDegree_monomial_one] at h1
  omega

/-- The relaxed feasible set: the moment matrices of the moments and of the auxiliary sequences
are at least `-τ`, the localized moments are within `η ∏ i ∈ S, ‖fᵢ‖₂` of the auxiliary ones,
and every coordinate is at most `R`. -/
structure InSet (A : System σ K) (ℓ : ℕ) (η τ R : ℝ) (x : Coord A ℓ → ℝ) : Prop where
  psd : MinEigGE (riesz (ys x)) ℓ (-τ)
  psd_aux : ∀ S, MinEigGE (riesz (ws x S)) (ℓ - A.degree S.1) (-τ)
  dist : ∀ S : sets A ℓ, ∑ m ∈ monomialsLE σ (ℓ - A.degree S.1), (loc A (ys x) S m - ws x S m) ^ 2
    ≤ (η * ∏ i ∈ S.1, coeffNorm (toReal (A.get i))) ^ 2
  box : ∀ i, |x i| ≤ R

omit [Algebra K ℝ] in
/-- The moments of a point of the box are at most `R`, if `R ≥ 1`. -/
theorem abs_ys_le {x : Coord A ℓ → ℝ} {R : ℝ} (hR : 1 ≤ R) (hx : ∀ i, |x i| ≤ R) (m : σ →₀ ℕ) :
    |ys x m| ≤ R := by
  unfold ys
  split_ifs
  · exact hx _
  · simpa using hR
  · simpa using zero_le_one.trans hR

/-- The objective `L_y q₀ + ∑ⱼ (L_y qⱼ)²`. -/
noncomputable def obj (q₀ : MvPolynomial σ ℝ) (qs : List (MvPolynomial σ ℝ))
    (y : (σ →₀ ℕ) → ℝ) : ℝ :=
  riesz y q₀ + (qs.map fun q ↦ riesz y q ^ 2).sum

/-! ### Competitors -/

/-- **Every competitor is in the set.** A pseudo-expectation that satisfies `A` up to `η`, with
moments at most `R_y`, gives a point of `InSet A ℓ η 0 R` whose moments are its own: the auxiliary
sequences are those of `SoS.PseudoExpectation.approxSatisfies_iff`. -/
theorem exists_lift (E : PseudoExpectation σ ℓ) {η : ℝ} (hη : 0 ≤ η)
    (hE : E.ApproxSatisfies A η 0) {Ry W F R : ℝ}
    (hRy : ∀ m : σ →₀ ℕ, m.degree ≤ ℓ → |E (monomial m 1)| ≤ Ry)
    (hW : ∀ S ∈ sets A ℓ, coeffNorm1 (toReal (A.prod S)) ≤ W)
    (hF : ∀ S ∈ sets A ℓ, ∏ i ∈ S, coeffNorm (toReal (A.get i)) ≤ F)
    (hR₁ : Ry ≤ R) (hR₂ : W * Ry + η * F ≤ R) :
    ∃ x : Coord A ℓ → ℝ, InSet A ℓ η 0 R x ∧
      ∀ m : σ →₀ ℕ, m.degree ≤ ℓ → ys x m = E (monomial m 1) := by
  classical
  have hdeg : ∀ S : Finset (Fin A.length), ∑ i ∈ S, max (A.get i).totalDegree 0 = A.degree S :=
    fun S ↦ by simp [System.degree]
  have hw : ∀ S : sets A ℓ, ∃ w : (σ →₀ ℕ) → ℝ, IsPSD (riesz w) (ℓ - A.degree S.1) ∧
      ∑ m ∈ monomialsLE σ (ℓ - A.degree S.1),
          (E (monomial m 1 * toReal (A.prod S.1)) - w m) ^ 2 ≤
        (η * ∏ i ∈ S.1, coeffNorm (toReal (A.get i))) ^ 2 := by
    intro S
    have := (E.approxSatisfies_iff A hη 0).1 hE S.1
      (by rw [hdeg]; exact degree_le_of_mem_sets S.2)
    simpa only [hdeg] using this
  choose w hwpsd hwdist using hw
  let x : Coord A ℓ → ℝ := fun
    | .inl m => E (monomial m.1 1)
    | .inr ⟨S, m⟩ => w S m.1
  have hys : ∀ m : σ →₀ ℕ, m.degree ≤ ℓ → ys x m = E (monomial m 1) := by
    intro m hm
    by_cases h0 : m = 0
    · subst h0
      rw [ys_zero, ← C_apply, C_1, E.map_one]
    · have hmem : m ∈ (monomialsLE σ ℓ).erase 0 := Finset.mem_erase.2 ⟨h0, mem_monomialsLE.2 hm⟩
      simp [ys, hmem, x]
  have hagree : ∀ h : MvPolynomial σ ℝ, h.totalDegree ≤ ℓ → riesz (ys x) h = E h := by
    intro h hh
    rw [riesz_apply, E.coe_apply, apply_eq_sum_coeff_mul E.toLinearMap h]
    exact Finset.sum_congr rfl fun m hm ↦ by rw [hys m ((le_totalDegree hm).trans hh)]
  have hws : ∀ (S : sets A ℓ) (m : σ →₀ ℕ), m ∈ monomialsLE σ (ℓ - A.degree S.1) →
      ws x S m = w S m := by
    intro S m hm
    simp [ws, hm, x]
  have hRy0 : 0 ≤ Ry := (abs_nonneg _).trans (hRy 0 (by simp))
  refine ⟨x, ⟨fun g hg ↦ ?_, fun S g hg ↦ ?_, fun S ↦ ?_, fun i ↦ ?_⟩, hys⟩
  · rw [hagree _ ((totalDegree_mul g g).trans (by omega))]
    simpa using E.map_mul_self_nonneg hg
  · have hgg : ∀ m ∈ (g * g).support, ws x S m = w S m := fun m hm ↦
      hws S m (mem_monomialsLE.2 ((le_totalDegree hm).trans
        ((totalDegree_mul g g).trans (by omega))))
    rw [riesz_congr hgg]
    simpa using hwpsd S g hg
  · refine le_of_eq_of_le (Finset.sum_congr rfl fun m hm ↦ ?_) (hwdist S)
    rw [loc, hagree _ (totalDegree_monomial_mul_prod_le (degree_le_of_mem_sets S.2)
      (mem_monomialsLE.1 hm)), hws S m hm]
  · rcases i with ⟨m, hm⟩ | ⟨S, m, hm⟩
    · exact (hRy m (mem_monomialsLE.1 (Finset.mem_of_mem_erase hm))).trans hR₁
    · -- `|w_S m| ≤ |Ẽ (xᵐ f_S)| + η F_S ≤ W R_y + η F`.
      change |w S m| ≤ R
      have hdist1 : (E (monomial m 1 * toReal (A.prod S.1)) - w S m) ^ 2 ≤
          (η * ∏ i ∈ S.1, coeffNorm (toReal (A.get i))) ^ 2 :=
        (Finset.single_le_sum (f := fun m ↦ (E (monomial m 1 * toReal (A.prod S.1)) - w S m) ^ 2)
          (fun _ _ ↦ sq_nonneg _) hm).trans (hwdist S)
      have hF0 : 0 ≤ ∏ i ∈ S.1, coeffNorm (toReal (A.get i)) :=
        Finset.prod_nonneg fun _ _ ↦ coeffNorm_nonneg _
      have h1 : |E (monomial m 1 * toReal (A.prod S.1)) - w S m| ≤
          η * ∏ i ∈ S.1, coeffNorm (toReal (A.get i)) := by
        have := sq_le_sq.1 hdist1
        rwa [abs_of_nonneg (mul_nonneg hη hF0)] at this
      have hdegm := totalDegree_monomial_mul_prod_le (degree_le_of_mem_sets S.2)
        (mem_monomialsLE.1 hm)
      have h2 : |E (monomial m 1 * toReal (A.prod S.1))| ≤ Ry * W := by
        rw [← hagree _ hdegm]
        refine (abs_riesz_le (B := Ry) fun m' hm' ↦ ?_).trans ?_
        · rw [hys m' ((le_totalDegree hm').trans hdegm)]
          exact hRy m' ((le_totalDegree hm').trans hdegm)
        · rw [coeffNorm1_monomial_mul]
          exact mul_le_mul_of_nonneg_left (hW S.1 S.2) hRy0
      have h3 : η * ∏ i ∈ S.1, coeffNorm (toReal (A.get i)) ≤ η * F :=
        mul_le_mul_of_nonneg_left (hF S.1 S.2) hη
      calc |w S m| = |E (monomial m 1 * toReal (A.prod S.1)) -
            (E (monomial m 1 * toReal (A.prod S.1)) - w S m)| := by ring_nf
        _ ≤ |E (monomial m 1 * toReal (A.prod S.1))| +
            |E (monomial m 1 * toReal (A.prod S.1)) - w S m| := abs_sub _ _
        _ ≤ Ry * W + η * F := add_le_add h2 (h1.trans h3)
        _ ≤ R := by linarith

omit [Fintype σ] [DecidableEq σ] in
/-- The objective of a point whose moments are those of `Ẽ` is the objective of `Ẽ`. -/
theorem obj_eq_of_agree (E : PseudoExpectation σ ℓ) {y : (σ →₀ ℕ) → ℝ}
    (hy : ∀ m : σ →₀ ℕ, m.degree ≤ ℓ → y m = E (monomial m 1)) {q₀ : MvPolynomial σ ℝ}
    {qs : List (MvPolynomial σ ℝ)} (hq : ∀ q ∈ q₀ :: qs, q.totalDegree ≤ ℓ) :
    obj q₀ qs y = E q₀ + (qs.map fun q ↦ E q ^ 2).sum := by
  have hagree : ∀ q ∈ q₀ :: qs, riesz y q = E q := by
    intro q hq'
    rw [riesz_apply, E.coe_apply, apply_eq_sum_coeff_mul E.toLinearMap q]
    exact Finset.sum_congr rfl fun m hm ↦ by
      rw [hy m ((le_totalDegree hm).trans (hq q hq'))]
  rw [obj, hagree q₀ List.mem_cons_self]
  congr 1
  exact congrArg List.sum (List.map_congr_left fun q hq' ↦ by
    rw [hagree q (List.mem_cons_of_mem _ hq')])

/-! ### Balls around competitors -/

omit [DecidableEq σ] in
/-- Moving the moments by at most `ρ` lowers the smallest eigenvalue of the moment matrix in
degree `D` by at most `ρ (n + 1)^D`. -/
theorem minEigGE_of_near {y y' : (σ →₀ ℕ) → ℝ} {D : ℕ} {ρ τ : ℝ}
    (hy' : MinEigGE (riesz y') D 0) (hnear : ∀ m, |y m - y' m| ≤ ρ)
    (hτ : ρ * (Fintype.card σ + 1) ^ D ≤ τ) : MinEigGE (riesz y) D (-τ) := by
  intro g hg
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hnear 0)
  have h0 : 0 ≤ riesz y' (g * g) := by simpa using hy' g hg
  have h1 := abs_riesz_sub_le (h := g * g) fun m _ ↦ hnear m
  have hcard : (g.support.card : ℝ) ≤ (Fintype.card σ + 1) ^ D := by
    have := (card_support_le g).trans (Nat.pow_le_pow_right (Nat.succ_pos _) (show
      g.totalDegree ≤ D by omega))
    exact_mod_cast this
  have key : ρ * coeffNorm1 (g * g) ≤ τ * coeffNorm g ^ 2 :=
    calc ρ * coeffNorm1 (g * g) ≤ ρ * coeffNorm1 g ^ 2 := by
          gcongr
          rw [sq]
          exact coeffNorm1_mul_le g g
      _ ≤ ρ * (g.support.card * coeffNorm g ^ 2) := by
          gcongr
          exact coeffNorm1_sq_le g
      _ ≤ ρ * ((Fintype.card σ + 1) ^ D * coeffNorm g ^ 2) := by gcongr
      _ = ρ * (Fintype.card σ + 1) ^ D * coeffNorm g ^ 2 := by ring
      _ ≤ τ * coeffNorm g ^ 2 := by gcongr
  linarith [neg_abs_le (riesz y (g * g) - riesz y' (g * g))]

/-- **A ball around every competitor.** Every point within `ρ` of a point of
`InSet A ℓ η 0 R₀`, coordinate by coordinate, is in `InSet A ℓ (η + γ) τ R`, for `ρ` small enough
compared to `τ`, `γ` and `R - R₀`. -/
theorem mem_of_near {x x' : Coord A ℓ → ℝ} {η γ τ ρ R₀ R W : ℝ} (hx' : InSet A ℓ η 0 R₀ x')
    (hη : 0 ≤ η) (hγ : 0 ≤ γ) (hρ : 0 ≤ ρ) (hnear : ∀ i, |x i - x' i| ≤ ρ)
    (hτ : ρ * (Fintype.card σ + 1) ^ ℓ ≤ τ)
    (hW : ∀ S ∈ sets A ℓ, coeffNorm1 (toReal (A.prod S)) ≤ W)
    (hdist : ∀ S ∈ sets A ℓ, (Fintype.card σ + 1 : ℝ) ^ ℓ * (ρ * (W + 1)) ^ 2 ≤
      (γ * ∏ i ∈ S, coeffNorm (toReal (A.get i))) ^ 2)
    (hR : R₀ + ρ ≤ R) : InSet A ℓ (η + γ) τ R x := by
  classical
  have hn1 : (1 : ℝ) ≤ Fintype.card σ + 1 := by
    linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ Fintype.card σ)]
  have hys : ∀ m, |ys x m - ys x' m| ≤ ρ := by
    intro m
    unfold ys
    split_ifs
    · exact hnear _
    all_goals simpa using hρ
  have hws : ∀ S m, |ws x S m - ws x' S m| ≤ ρ := by
    intro S m
    unfold ws
    split_ifs
    · exact hnear _
    · simpa using hρ
  have hτ' : ∀ D ≤ ℓ, ρ * (Fintype.card σ + 1) ^ D ≤ τ := fun D hD ↦
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 hD) hρ).trans hτ
  refine ⟨minEigGE_of_near (by simpa using hx'.psd) hys hτ,
    fun S ↦ minEigGE_of_near (by simpa using hx'.psd_aux S) (hws S) (hτ' _ (Nat.sub_le _ _)),
    fun S ↦ ?_, fun i ↦ ?_⟩
  · set D := ℓ - A.degree S.1
    set F := ∏ i ∈ S.1, coeffNorm (toReal (A.get i))
    have hF : 0 ≤ F := Finset.prod_nonneg fun _ _ ↦ coeffNorm_nonneg _
    set v' : (σ →₀ ℕ) → ℝ := fun m ↦ loc A (ys x') S m - ws x' S m
    set e : (σ →₀ ℕ) → ℝ := fun m ↦ (loc A (ys x) S m - ws x S m) - v' m
    have he : ∀ m, |e m| ≤ ρ * (W + 1) := by
      intro m
      have h1 : |loc A (ys x) S m - loc A (ys x') S m| ≤ ρ * W := by
        refine (abs_riesz_sub_le fun m' _ ↦ hys m').trans ?_
        rw [coeffNorm1_monomial_mul]
        exact mul_le_mul_of_nonneg_left (hW S.1 S.2) hρ
      calc |e m| = |(loc A (ys x) S m - loc A (ys x') S m) - (ws x S m - ws x' S m)| := by
            simp only [e, v']
            ring_nf
        _ ≤ |loc A (ys x) S m - loc A (ys x') S m| + |ws x S m - ws x' S m| := abs_sub _ _
        _ ≤ ρ * W + ρ := add_le_add h1 (hws S m)
        _ = ρ * (W + 1) := by ring
    have hv' : ‖vecLE D v'‖ ≤ η * F := by
      refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hη hF)).1 ?_
      rw [norm_vecLE_sq]
      exact hx'.dist S
    have he' : ‖vecLE D e‖ ≤ γ * F := by
      refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hγ hF)).1 ?_
      rw [norm_vecLE_sq]
      calc ∑ m ∈ monomialsLE σ D, e m ^ 2 ≤ ∑ _m ∈ monomialsLE σ D, (ρ * (W + 1)) ^ 2 :=
            Finset.sum_le_sum fun m _ ↦ by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (he m) 2
        _ = (monomialsLE σ D).card * (ρ * (W + 1)) ^ 2 := by simp
        _ ≤ (Fintype.card σ + 1 : ℝ) ^ ℓ * (ρ * (W + 1)) ^ 2 := by
            gcongr
            exact_mod_cast (card_monomialsLE_le D).trans
              (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.sub_le _ _))
        _ ≤ (γ * F) ^ 2 := hdist S.1 S.2
    have hsum : vecLE D v' + vecLE D e = vecLE D fun m ↦ loc A (ys x) S m - ws x S m := by
      ext m
      simp [e, vecLE]
    calc ∑ m ∈ monomialsLE σ D, (loc A (ys x) S m - ws x S m) ^ 2
        = ‖vecLE D v' + vecLE D e‖ ^ 2 := by rw [hsum, norm_vecLE_sq]
      _ ≤ (η * F + γ * F) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) ((norm_add_le _ _).trans (add_le_add hv' he')) 2
      _ = ((η + γ) * F) ^ 2 := by ring
  · calc |x i| = |x' i + (x i - x' i)| := by ring_nf
      _ ≤ |x' i| + |x i - x' i| := abs_add_le _ _
      _ ≤ R₀ + ρ := add_le_add (hx'.box i) (hnear i)
      _ ≤ R := hR

/-! ### The objective -/

omit [Fintype σ] [DecidableEq σ] in
/-- Termwise bounds bound the difference of two sums over a list. -/
theorem abs_sum_map_sub_le {α : Type*} (l : List α) (f g c : α → ℝ)
    (h : ∀ a ∈ l, |f a - g a| ≤ c a) :
    |(l.map f).sum - (l.map g).sum| ≤ (l.map c).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    calc |f a + (l.map f).sum - (g a + (l.map g).sum)|
        = |(f a - g a) + ((l.map f).sum - (l.map g).sum)| := by ring_nf
      _ ≤ |f a - g a| + |(l.map f).sum - (l.map g).sum| := abs_add_le _ _
      _ ≤ c a + (l.map c).sum := add_le_add h1 h2

omit [Fintype σ] [DecidableEq σ] in
/-- **The objective is Lipschitz** on bounded moments: if `y` and `y'` differ by at most `ρ` and
are at most `B` up to degree `ℓ`, their objectives differ by at most
`ρ (‖q₀‖₁ + 2B ∑ⱼ ‖qⱼ‖₁²)`. -/
theorem abs_obj_sub_le {q₀ : MvPolynomial σ ℝ} {qs : List (MvPolynomial σ ℝ)}
    {y y' : (σ →₀ ℕ) → ℝ} {ρ B : ℝ} (hq : ∀ q ∈ q₀ :: qs, q.totalDegree ≤ ℓ)
    (hy : ∀ m : σ →₀ ℕ, m.degree ≤ ℓ → |y m - y' m| ≤ ρ ∧ |y m| ≤ B ∧ |y' m| ≤ B) :
    |obj q₀ qs y - obj q₀ qs y'| ≤
      ρ * (coeffNorm1 q₀ + 2 * B * (qs.map fun q ↦ coeffNorm1 q ^ 2).sum) := by
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hy 0 (by simp)).1
  have hs : ∀ q ∈ q₀ :: qs, ∀ m ∈ q.support, |y m - y' m| ≤ ρ ∧ |y m| ≤ B ∧ |y' m| ≤ B :=
    fun q hq' m hm ↦ hy m ((le_totalDegree hm).trans (hq q hq'))
  have hsq : ∀ q ∈ qs, |riesz y q ^ 2 - riesz y' q ^ 2| ≤ ρ * (2 * B * coeffNorm1 q ^ 2) := by
    intro q hq'
    have hm := hs q (List.mem_cons_of_mem _ hq')
    have h1 := abs_riesz_sub_le fun m hm' ↦ (hm m hm').1
    have h2 := abs_riesz_le (y := y) fun m hm' ↦ (hm m hm').2.1
    have h3 := abs_riesz_le (y := y') fun m hm' ↦ (hm m hm').2.2
    rw [show riesz y q ^ 2 - riesz y' q ^ 2 = (riesz y q - riesz y' q) * (riesz y q + riesz y' q)
      by ring, abs_mul]
    calc |riesz y q - riesz y' q| * |riesz y q + riesz y' q|
        ≤ (ρ * coeffNorm1 q) * (B * coeffNorm1 q + B * coeffNorm1 q) :=
          mul_le_mul h1 ((abs_add_le _ _).trans (add_le_add h2 h3)) (abs_nonneg _)
            (mul_nonneg hρ (coeffNorm1_nonneg _))
      _ = ρ * (2 * B * coeffNorm1 q ^ 2) := by ring
  have hlist := abs_sum_map_sub_le qs _ _ _ hsq
  have h0 := abs_riesz_sub_le fun m hm ↦ (hs q₀ List.mem_cons_self m hm).1
  rw [List.sum_map_mul_left, List.sum_map_mul_left] at hlist
  calc |obj q₀ qs y - obj q₀ qs y'|
      = |(riesz y q₀ - riesz y' q₀) + ((qs.map fun q ↦ riesz y q ^ 2).sum -
          (qs.map fun q ↦ riesz y' q ^ 2).sum)| := by
        rw [obj, obj]
        ring_nf
    _ ≤ |riesz y q₀ - riesz y' q₀| + |(qs.map fun q ↦ riesz y q ^ 2).sum -
          (qs.map fun q ↦ riesz y' q ^ 2).sum| := abs_add_le _ _
    _ ≤ ρ * coeffNorm1 q₀ + ρ * (2 * B * (qs.map fun q ↦ coeffNorm1 q ^ 2).sum) :=
        add_le_add h0 hlist
    _ = _ := by ring

/-! ### The output -/

/-- Mixing moments `y` with moments `μ` in the ratio `1 : t`: `(y + t μ) / (1 + t)`. -/
noncomputable def mix (t : ℝ) (μ y : (σ →₀ ℕ) → ℝ) : (σ →₀ ℕ) → ℝ :=
  (1 + t)⁻¹ • (y + t • μ)

omit [Fintype σ] [DecidableEq σ] in
theorem mix_apply (t : ℝ) (μ y : (σ →₀ ℕ) → ℝ) (m : σ →₀ ℕ) :
    mix t μ y m = (y m + t * μ m) / (1 + t) := by
  simp [mix, div_eq_inv_mul]

omit [Fintype σ] [DecidableEq σ] in
theorem riesz_mix (t : ℝ) (μ y : (σ →₀ ℕ) → ℝ) :
    riesz (mix t μ y) = (1 + t)⁻¹ • (riesz y + t • riesz μ) := by
  rw [mix, riesz_smul, riesz_add, riesz_smul]

/-- **The output.** Let `x` be in the relaxed set `InSet A ℓ (η + γ') τ R`, and `μ` moments with
`μ 0 = 1` whose moment matrix is at least `κ`, with `τ ≤ t κ`. Then mixing the moments of `x`
with `μ` in the ratio `1 : t` gives an exact pseudo-expectation, which satisfies `A` up to
`η + γ` when `t` is small enough. The constant constraints must be nonnegative. -/
theorem output {x : Coord A ℓ → ℝ} {η γ' γ τ R t κ Dμ W : ℝ}
    (hx : InSet A ℓ (η + γ') τ R x) {μ : (σ →₀ ℕ) → ℝ} (hμ0 : μ 0 = 1)
    (hμ : MinEigGE (riesz μ) ℓ κ) (hμb : ∀ m : σ →₀ ℕ, m.degree ≤ ℓ → |μ m| ≤ Dμ)
    (ht : 0 < t) (hτ : τ ≤ t * κ) (hη : 0 ≤ η) (hγ' : 0 ≤ γ') (hγ : γ' ≤ γ)
    (hW : ∀ S ∈ sets A ℓ, coeffNorm1 (toReal (A.prod S)) ≤ W)
    (hdist : ∀ S ∈ sets A ℓ, (Fintype.card σ + 1 : ℝ) ^ ℓ * (t * ((W + 1) * Dμ)) ^ 2 ≤
      ((γ - γ') * ∏ i ∈ S, coeffNorm (toReal (A.get i))) ^ 2)
    (hA : ∀ i, (A.get i).totalDegree = 0 → 0 ≤ algebraMap K ℝ ((A.get i).coeff 0)) :
    ∃ (h0 : mix t μ (ys x) 0 = 1) (hpsd : IsPSD (riesz (mix t μ (ys x))) ℓ),
      (PseudoExpectation.ofMoments _ h0 hpsd).ApproxSatisfies A (η + γ) 0 := by
  classical
  have ht1 : 0 < 1 + t := by linarith
  have hDμ : 0 ≤ Dμ := (abs_nonneg _).trans (hμb 0 (by simp))
  -- A mixture is positive semidefinite in every degree `D ≤ ℓ` where `z` is at least `-τ`.
  have hpsdmix : ∀ (z : (σ →₀ ℕ) → ℝ) (D : ℕ), D ≤ ℓ → MinEigGE (riesz z) D (-τ) →
      IsPSD (riesz (mix t μ z)) D := by
    intro z D hD hz
    rw [riesz_mix]
    refine IsPSD.smul ?_ (inv_nonneg.2 ht1.le)
    exact (hz.add ((hμ.mono hD le_rfl).smul ht.le)).isPSD (by linarith)
  have h0 : mix t μ (ys x) 0 = 1 := by
    rw [mix_apply, ys_zero, hμ0, mul_one, div_self ht1.ne']
  refine ⟨h0, hpsdmix _ ℓ le_rfl hx.psd, ?_⟩
  set E := PseudoExpectation.ofMoments _ h0 (hpsdmix _ ℓ le_rfl hx.psd)
  rw [PseudoExpectation.approxSatisfies_iff_of_nonneg_const E A (η + γ) hA]
  intro S hS h hh hd
  rcases S.eq_empty_or_nonempty with rfl | hne
  · -- No constraints: `Ẽ h ≥ 0`.
    simp only [Finset.prod_empty, mul_one, System.prod_empty, toReal_one]
    have h1 := E.nonneg_of_isSumSq hh (by simpa [System.degree] using hd)
    have h2 : 0 ≤ (η + γ) * coeffNorm h := mul_nonneg (by linarith) (coeffNorm_nonneg h)
    linarith
  · have hSmem : S ∈ sets A ℓ := by
      unfold sets
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hne, hS, by omega⟩
    set S' : sets A ℓ := ⟨S, hSmem⟩
    set D := ℓ - A.degree S
    set F := ∏ i ∈ S, coeffNorm (toReal (A.get i))
    have hF : 0 ≤ F := Finset.prod_nonneg fun _ _ ↦ coeffNorm_nonneg _
    set w := mix t μ (ws x S')
    have hwpsd : IsPSD (riesz w) D := hpsdmix _ D (Nat.sub_le _ _) (hx.psd_aux S')
    -- The localized moments of the output are within `(η + γ) F` of `w`.
    set a : (σ →₀ ℕ) → ℝ := fun m ↦ loc A (ys x) S m - ws x S' m
    set b : (σ →₀ ℕ) → ℝ := fun m ↦ loc A μ S m - μ m
    have hab : ∀ m, E (monomial m 1 * toReal (A.prod S)) - w m = (a m + t * b m) / (1 + t) := by
      intro m
      have : E (monomial m 1 * toReal (A.prod S)) =
          (loc A (ys x) S m + t * loc A μ S m) / (1 + t) := by
        simp only [E, PseudoExpectation.ofMoments_apply, riesz_mix, LinearMap.smul_apply,
          LinearMap.add_apply, smul_eq_mul, loc]
        field_simp
      rw [this]
      simp only [w, mix_apply, a, b]
      field_simp
      ring
    have ha : ‖vecLE D a‖ ≤ (η + γ') * F := by
      refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) hF)).1 ?_
      rw [norm_vecLE_sq]
      exact hx.dist S'
    have hb : t * ‖vecLE D b‖ ≤ (γ - γ') * F := by
      have hbm : ∀ m ∈ monomialsLE σ D, |b m| ≤ (W + 1) * Dμ := by
        intro m hm
        have hdegm := totalDegree_monomial_mul_prod_le (degree_le_of_mem_sets hSmem)
          (mem_monomialsLE.1 hm)
        have h1 : |loc A μ S m| ≤ Dμ * W := by
          refine (abs_riesz_le (B := Dμ) fun m' hm' ↦
            hμb m' ((le_totalDegree hm').trans hdegm)).trans ?_
          rw [coeffNorm1_monomial_mul]
          exact mul_le_mul_of_nonneg_left (hW S hSmem) hDμ
        have h2 : |μ m| ≤ Dμ := hμb m ((mem_monomialsLE.1 hm).trans (Nat.sub_le _ _))
        calc |b m| ≤ |loc A μ S m| + |μ m| := abs_sub _ _
          _ ≤ Dμ * W + Dμ := add_le_add h1 h2
          _ = (W + 1) * Dμ := by ring
      refine (sq_le_sq₀ (mul_nonneg ht.le (norm_nonneg _))
        (mul_nonneg (by linarith) hF)).1 ?_
      rw [mul_pow, norm_vecLE_sq]
      calc t ^ 2 * ∑ m ∈ monomialsLE σ D, b m ^ 2
          ≤ t ^ 2 * ∑ _m ∈ monomialsLE σ D, ((W + 1) * Dμ) ^ 2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m hm ↦ by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hbm m hm) 2) (sq_nonneg t)
        _ = (monomialsLE σ D).card * (t * ((W + 1) * Dμ)) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
        _ ≤ (Fintype.card σ + 1 : ℝ) ^ ℓ * (t * ((W + 1) * Dμ)) ^ 2 := by
            gcongr
            exact_mod_cast (card_monomialsLE_le D).trans
              (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.sub_le _ _))
        _ ≤ ((γ - γ') * F) ^ 2 := hdist S hSmem
    have hvec : (vecLE D fun m ↦ E (monomial m 1 * toReal (A.prod S)) - w m) =
        (1 + t)⁻¹ • (vecLE D a + t • vecLE D b) := by
      ext m
      simp only [vecLE, hab]
      simp [div_eq_inv_mul]
      ring
    have hd2 : ∑ m ∈ monomialsLE σ D, (E (monomial m 1 * toReal (A.prod S)) - w m) ^ 2 ≤
        ((η + γ) * F) ^ 2 := by
      rw [← norm_vecLE_sq, hvec, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht1]
      have hle : ‖vecLE D a + t • vecLE D b‖ ≤ (η + γ) * F := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        linarith
      have hinv : (1 + t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      calc (1 + t)⁻¹ * ‖vecLE D a + t • vecLE D b‖ ≤ 1 * ‖vecLE D a + t • vecLE D b‖ :=
            mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
        _ ≤ (η + γ) * F := by rw [one_mul]; exact hle
    have happ := (approxNonneg_iff (E.toLinearMap ∘ₗ LinearMap.mulRight ℝ (toReal (A.prod S))) D
      (mul_nonneg (by linarith) hF)).2 ⟨w, hwpsd, hd2⟩ h hh (by omega)
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply] at happ
    calc -((η + γ) * coeffNorm h * F) = -((η + γ) * F * coeffNorm h) := by ring
      _ ≤ _ := happ

omit [Algebra K ℝ] in
/-- **The objective barely moves** when mixing in `μ` with a small weight `t`. -/
theorem abs_obj_mix_sub_le {x : Coord A ℓ → ℝ} {R t Dμ : ℝ} (hR : 1 ≤ R)
    (hx : ∀ i, |x i| ≤ R) {μ : (σ →₀ ℕ) → ℝ} (hμb : ∀ m : σ →₀ ℕ, m.degree ≤ ℓ → |μ m| ≤ Dμ)
    (ht : 0 ≤ t) {q₀ : MvPolynomial σ ℝ} {qs : List (MvPolynomial σ ℝ)}
    (hq : ∀ q ∈ q₀ :: qs, q.totalDegree ≤ ℓ) :
    |obj q₀ qs (mix t μ (ys x)) - obj q₀ qs (ys x)| ≤
      t * (R + Dμ) * (coeffNorm1 q₀ + 2 * (R + Dμ) * (qs.map fun q ↦ coeffNorm1 q ^ 2).sum) := by
  have hDμ : 0 ≤ Dμ := (abs_nonneg _).trans (hμb 0 (by simp))
  have ht1 : 0 < 1 + t := by linarith
  refine abs_obj_sub_le hq fun m hm ↦ ⟨?_, ?_, ?_⟩
  · have e : mix t μ (ys x) m - ys x m = t / (1 + t) * (μ m - ys x m) := by
      rw [mix_apply]
      field_simp
      ring
    rw [e, abs_mul, abs_div, abs_of_nonneg ht, abs_of_pos ht1]
    have h1 : |μ m - ys x m| ≤ R + Dμ := (abs_sub (μ m) (ys x m)).trans
      (by linarith [hμb m hm, abs_ys_le hR hx m])
    have h2 : t / (1 + t) ≤ t := div_le_self ht (by linarith)
    calc t / (1 + t) * |μ m - ys x m| ≤ t * (R + Dμ) :=
          mul_le_mul h2 h1 (abs_nonneg _) ht
      _ = t * (R + Dμ) := rfl
  · rw [mix_apply, abs_div, abs_of_pos ht1, div_le_iff₀ ht1]
    calc |ys x m + t * μ m| ≤ |ys x m| + |t * μ m| := abs_add_le _ _
      _ = |ys x m| + t * |μ m| := by rw [abs_mul, abs_of_nonneg ht]
      _ ≤ R + t * Dμ := add_le_add (abs_ys_le hR hx m)
          (mul_le_mul_of_nonneg_left (hμb m hm) ht)
      _ ≤ (R + Dμ) * (1 + t) := by nlinarith
  · linarith [abs_ys_le hR hx m]

end SoS.Lifted
