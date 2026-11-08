module

public import BMW26.Model
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Fintype.Powerset

/-!
# The hypercube: flips, characters, Fourier coefficients, energies

Functions on the hypercube `Cube m = Fin m → Bool` (bits stand for signs: `false ↦ 1`,
`true ↦ -1`, `BMW26.sgn`), and the quantities that the spectral and sum-of-squares parts are
stated in.

* `BMW26.flip x i`, `BMW26.lowPt x i`: `x` with coordinate `i` flipped, and set to `false`.
* `BMW26.chi S x`: the character `χ_S(x) = ∏_{i ∈ S} (-1)^{xᵢ}`; `BMW26.fourier g S` the
  Fourier coefficient `ĝ(S) = 2^{-m} ∑ₓ g(x) χ_S(x)`, and `BMW26.lowProj r g` the projection of
  `g` on the characters of degree at most `r`.
* **Energies** (`BMW26.energy w g`): edge weights `w i x` are read at the lower endpoint of the edge
  `{x, flip x i}` (the one with `xᵢ = false`), and `energy w g = ∑ᵢ ∑_{xᵢ = false} w i x (g x -
  g (flip x i))²`. The all-one weights give the hypercube `Q_m` (its energy is `n ⟨g, L g⟩` in the
  paper's normalized inner product, with `n = 2^m`); the indicator weights of a graph
  (`BMW26.graphW`) give the graph; `BMW26.halfW i w` removes the edges of direction `i`.
* `BMW26.deg w x` and `BMW26.lap w g`: degrees and the Laplacian, `∑ₓ g x · lap w g x =
  energy w g`.
* `BMW26.SpecClose w w₀ p ε D`: the spectral comparison used by the sum-of-squares proof,
  `|energy w g - p energy w₀ g| ≤ ε p energy w₀ g + ∑ₓ D x g(x)²` for every `g`. The error is
  diagonal: on `±1`-valued `g` it is the constant `∑ₓ D x`.
-/

@[expose] public section

namespace BMW26

open Finset

variable {m : ℕ}

/-! ### Flips -/

/-- `x` with its coordinate `i` flipped. -/
def flip (x : Cube m) (i : Fin m) : Cube m := Function.update x i (!x i)

/-- `x` with its coordinate `i` set to `false`: the lower endpoint of the edge `{x, flip x i}`, at
which edge weights are read. -/
def lowPt (x : Cube m) (i : Fin m) : Cube m := Function.update x i false

/-! ### Characters and Fourier coefficients -/

/-- The character `χ_S(x) = ∏_{i ∈ S} (-1)^{xᵢ}`. -/
def chi (S : Finset (Fin m)) (x : Cube m) : ℝ := ∏ i ∈ S, sgn (x i)

/-- The Fourier coefficient `ĝ(S) = 2^{-m} ∑ₓ g(x) χ_S(x)`. -/
noncomputable def fourier (g : Cube m → ℝ) (S : Finset (Fin m)) : ℝ :=
  (∑ x, g x * chi S x) / 2 ^ m

/-- The projection of `g` on the characters of degree at most `r`. -/
noncomputable def lowProj (r : ℕ) (g : Cube m → ℝ) (x : Cube m) : ℝ :=
  ∑ S ∈ univ.filter (fun S : Finset (Fin m) ↦ S.card ≤ r), fourier g S * chi S x

/-! ### Edge weights and energies -/

/-- The **energy** of `g` for the edge weights `w`: `∑ᵢ ∑_{xᵢ = false} w i x (g x - g (flip x i))²`.
The weight of the edge `{x, flip x i}` is `w i x` at its lower endpoint `x` (`xᵢ = false`); the
values of `w i x` with `xᵢ = true` play no role. -/
noncomputable def energy (w : Fin m → Cube m → ℝ) (g : Cube m → ℝ) : ℝ :=
  ∑ i, ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), w i x * (g x - g (flip x i)) ^ 2

open Classical in
/-- The indicator edge weights of a graph `H` on the hypercube: `1` on the edges of `H`. -/
noncomputable def graphW (H : SimpleGraph (Cube m)) (i : Fin m) (x : Cube m) : ℝ :=
  if H.Adj x (flip x i) then 1 else 0

/-- The weights `w` without the edges of direction `i`: the two half-cubes `xᵢ = false` and
`xᵢ = true`. -/
def halfW (i : Fin m) (w : Fin m → Cube m → ℝ) (j : Fin m) (x : Cube m) : ℝ :=
  if j = i then 0 else w j x

/-- The weighted degree of `x`: the sum of the weights of the `m` edges at `x`. -/
def deg (w : Fin m → Cube m → ℝ) (x : Cube m) : ℝ := ∑ i, w i (lowPt x i)

/-- The Laplacian of the weights `w` applied to `g`:
`(L_w g)(x) = ∑ᵢ w i (lowPt x i) (g x - g (flip x i))`. -/
def lap (w : Fin m → Cube m → ℝ) (g : Cube m → ℝ) (x : Cube m) : ℝ :=
  ∑ i, w i (lowPt x i) * (g x - g (flip x i))

/-- **Spectral closeness with a diagonal error**: for every `g`,
`|energy w g - p energy w₀ g| ≤ ε p energy w₀ g + ∑ₓ D x g(x)²`. -/
def SpecClose (w w₀ : Fin m → Cube m → ℝ) (p ε : ℝ) (D : Cube m → ℝ) : Prop :=
  ∀ g : Cube m → ℝ, |energy w g - p * energy w₀ g| ≤ ε * p * energy w₀ g + ∑ x, D x * g x ^ 2

/-! ### Basic facts -/

theorem flip_flip (x : Cube m) (i : Fin m) : flip (flip x i) i = x := by
  funext j
  by_cases h : j = i
  · subst h; simp [BMW26.flip]
  · simp [BMW26.flip, Function.update_of_ne h]

theorem flip_apply_self (x : Cube m) (i : Fin m) : flip x i i = !x i := by
  simp [BMW26.flip]

theorem flip_apply_ne (x : Cube m) {i j : Fin m} (h : j ≠ i) : flip x i j = x j := by
  simp [BMW26.flip, Function.update_of_ne h]

theorem flip_ne_self (x : Cube m) (i : Fin m) : flip x i ≠ x := by
  intro h
  have := congrFun h i
  rw [flip_apply_self] at this
  cases hx : x i <;> simp [hx] at this

theorem flip_injective (i : Fin m) : Function.Injective fun x : Cube m ↦ flip x i := by
  intro x y h
  simpa [flip_flip] using congrArg (fun z ↦ flip z i) h

theorem lowPt_flip (x : Cube m) (i : Fin m) : lowPt (flip x i) i = lowPt x i := by
  simp [lowPt, BMW26.flip]

theorem lowPt_of_false {x : Cube m} {i : Fin m} (h : x i = false) : lowPt x i = x := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [lowPt, h]
  · simp [lowPt, Function.update_of_ne hj]

theorem hammingDist_flip (x : Cube m) (i : Fin m) : hammingDist x (flip x i) = 1 := by
  unfold hammingDist
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  by_cases h : j = i
  · subst h; simp [flip_apply_self]
  · simp [flip_apply_ne x h, h]

/-- The neighbours of `x` in `Q_m` are the flips of `x`. -/
theorem cube_adj_iff {x y : Cube m} : (cube m).Adj x y ↔ ∃ i, y = flip x i := by
  constructor
  · intro h
    change hammingDist x y = 1 at h
    unfold hammingDist at h
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h
    refine ⟨i, funext fun j ↦ ?_⟩
    have hj := Finset.ext_iff.1 hi j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hj
    by_cases h : j = i
    · subst h
      rw [flip_apply_self]
      have := hj.2 rfl
      cases hx : x j <;> cases hy : y j <;> simp_all
    · rw [flip_apply_ne x h]
      by_contra hne
      exact h (hj.1 (Ne.symm hne))
  · rintro ⟨i, rfl⟩
    exact hammingDist_flip x i

theorem sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by
  cases b <;> simp [sgn]

theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by
  cases b <;> simp [sgn]

/-- A character as a product over all coordinates. -/
theorem Cube.chi_eq_prod_univ (S : Finset (Fin m)) (x : Cube m) :
    chi S x = ∏ j, if j ∈ S then sgn (x j) else 1 := by
  simp [chi]

theorem chi_sq (S : Finset (Fin m)) (x : Cube m) : chi S x ^ 2 = 1 := by
  unfold chi
  rw [← Finset.prod_pow]
  simp [sgn_sq]

theorem chi_mul_chi (S T : Finset (Fin m)) (x : Cube m) :
    chi S x * chi T x = chi (symmDiff S T) x := by
  rw [Cube.chi_eq_prod_univ, Cube.chi_eq_prod_univ, Cube.chi_eq_prod_univ,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  have h2 : sgn (x j) * sgn (x j) = 1 := by rw [← sq]; exact sgn_sq _
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp [hS, hT, Finset.mem_symmDiff, h2]

theorem chi_flip (S : Finset (Fin m)) (x : Cube m) (i : Fin m) :
    chi S (flip x i) = if i ∈ S then -chi S x else chi S x := by
  unfold chi
  split_ifs with h
  · rw [← Finset.mul_prod_erase S _ h, ← Finset.mul_prod_erase S _ h, flip_apply_self, sgn_not,
      neg_mul]
    congr 2
    exact Finset.prod_congr rfl fun j hj ↦ by rw [flip_apply_ne x (Finset.ne_of_mem_erase hj)]
  · refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [flip_apply_ne x (by rintro rfl; exact h hj)]

theorem chi_singleton (i : Fin m) (x : Cube m) : chi {i} x = sgn (x i) := by
  simp [chi]

/-- The sum of a character: `2^m` for the trivial one, `0` otherwise. -/
theorem Cube.sum_chi (U : Finset (Fin m)) :
    ∑ x : Cube m, chi U x = if U = ∅ then (2 : ℝ) ^ m else 0 := by
  simp_rw [Cube.chi_eq_prod_univ]
  rw [← Fintype.prod_sum (fun j (b : Bool) ↦ if j ∈ U then sgn b else 1)]
  have h : ∀ j, ∑ b : Bool, (if j ∈ U then sgn b else 1) = if j ∈ U then (0 : ℝ) else 2 := by
    intro j
    split_ifs <;> simp [sgn]
  simp_rw [h]
  split_ifs with hU
  · subst hU; simp
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hU
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

/-- **Orthogonality of characters.** -/
theorem sum_chi_mul_chi (S T : Finset (Fin m)) :
    ∑ x, chi S x * chi T x = if S = T then (2 : ℝ) ^ m else 0 := by
  simp_rw [chi_mul_chi]
  rw [Cube.sum_chi]
  have h : symmDiff S T = ∅ ↔ S = T := symmDiff_eq_bot
  simp only [h]

/-- **Orthogonality of points.** -/
theorem sum_chi_mul_chi_pts (x y : Cube m) :
    ∑ S, chi S x * chi S y = if x = y then (2 : ℝ) ^ m else 0 := by
  have h1 : ∀ S : Finset (Fin m), chi S x * chi S y = ∏ i ∈ S, (sgn (x i) * sgn (y i)) := by
    intro S
    simp [chi, Finset.prod_mul_distrib]
  simp_rw [h1]
  rw [show (∑ S : Finset (Fin m), ∏ i ∈ S, (sgn (x i) * sgn (y i))) =
      ∏ i, (1 + sgn (x i) * sgn (y i)) by rw [Finset.prod_one_add, Finset.powerset_univ]]
  have h2 : ∀ i, 1 + sgn (x i) * sgn (y i) = if x i = y i then 2 else 0 := by
    intro i
    cases x i <;> cases y i <;> simp [sgn] <;> norm_num
  simp_rw [h2]
  split_ifs with hxy
  · subst hxy; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- `∑ₓ g(x) χ_S(x) = 2^m ĝ(S)`. -/
theorem Cube.sum_mul_chi (g : Cube m → ℝ) (S : Finset (Fin m)) :
    ∑ x, g x * chi S x = 2 ^ m * fourier g S := by
  unfold fourier
  field_simp

/-- **Fourier expansion.** -/
theorem sum_fourier_mul_chi (g : Cube m → ℝ) (x : Cube m) :
    ∑ S, fourier g S * chi S x = g x := by
  have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
  apply mul_left_cancel₀ h2m
  calc 2 ^ m * ∑ S, fourier g S * chi S x = ∑ S, (∑ y, g y * chi S y) * chi S x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ ↦ ?_
        rw [Cube.sum_mul_chi]
        ring
    _ = ∑ y, g y * ∑ S, chi S y * chi S x := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun S _ ↦ ?_
        ring
    _ = 2 ^ m * g x := by
        simp_rw [sum_chi_mul_chi_pts]
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        ring

/-- **Plancherel.** -/
theorem sum_mul_eq_sum_fourier (g h : Cube m → ℝ) :
    ∑ x, g x * h x = 2 ^ m * ∑ S, fourier g S * fourier h S := by
  calc ∑ x, g x * h x = ∑ x, g x * ∑ S, fourier h S * chi S x := by
        simp_rw [sum_fourier_mul_chi]
    _ = ∑ S, fourier h S * ∑ x, g x * chi S x := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun S _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
        ring
    _ = 2 ^ m * ∑ S, fourier g S * fourier h S := by
        simp_rw [Cube.sum_mul_chi, Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ ↦ ?_
        ring

/-- **Parseval.** -/
theorem sum_sq_eq_sum_fourier (g : Cube m → ℝ) :
    ∑ x, g x ^ 2 = 2 ^ m * ∑ S, fourier g S ^ 2 := by
  simp_rw [sq]
  exact sum_mul_eq_sum_fourier g g

theorem fourier_lowProj (r : ℕ) (g : Cube m → ℝ) (S : Finset (Fin m)) :
    fourier (lowProj r g) S = if S.card ≤ r then fourier g S else 0 := by
  have key : ∑ x, lowProj r g x * chi S x =
      ∑ T ∈ univ.filter (fun T : Finset (Fin m) ↦ T.card ≤ r),
        fourier g T * ∑ x, chi T x * chi S x := by
    unfold lowProj
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [fourier, key]
  simp_rw [sum_chi_mul_chi, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs
  · field_simp
  · simp

theorem fourier_sub (g h : Cube m → ℝ) (S : Finset (Fin m)) :
    fourier (g - h) S = fourier g S - fourier h S := by
  simp [fourier, sub_mul, Finset.sum_sub_distrib, sub_div]

/-- Reindexing a sum over the cube by the flip of a coordinate. -/
theorem Cube.sum_comp_flip (i : Fin m) (F : Cube m → ℝ) : ∑ x, F (flip x i) = ∑ x, F x :=
  Fintype.sum_bijective (fun x ↦ flip x i)
    ⟨flip_injective i, fun y ↦ ⟨flip y i, flip_flip y i⟩⟩ _ _ (fun _ ↦ rfl)

/-- A sum over the cube as a sum over the edges of direction `i`, at their lower endpoints. -/
theorem Cube.sum_eq_sum_filter_false (i : Fin m) (F : Cube m → ℝ) :
    ∑ x, F x = ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), (F x + F (flip x i)) := by
  rw [Finset.sum_add_distrib,
    ← Finset.sum_filter_add_sum_filter_not univ (fun x : Cube m ↦ x i = false)]
  congr 1
  refine Finset.sum_nbij' (fun x ↦ flip x i) (fun x ↦ flip x i) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [flip_apply_self]
    simpa using hx
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [flip_apply_self, hx]
    simp
  · intro x _; exact flip_flip x i
  · intro x _; exact flip_flip x i
  · intro x _; rw [flip_flip]

/-- Half of a flip-invariant sum. -/
theorem Cube.sum_filter_false_eq_half (i : Fin m) (G : Cube m → ℝ)
    (hG : ∀ x, G (flip x i) = G x) :
    ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), G x = (∑ x, G x) / 2 := by
  rw [Cube.sum_eq_sum_filter_false i G]
  simp_rw [hG, ← two_mul]
  rw [← Finset.mul_sum]
  ring

/-- The Fourier coefficients of the derivative in direction `i`. -/
theorem Cube.fourier_sub_flip (g : Cube m → ℝ) (i : Fin m) (S : Finset (Fin m)) :
    fourier (fun x ↦ g x - g (flip x i)) S = if i ∈ S then 2 * fourier g S else 0 := by
  have h1 : ∑ x, g (flip x i) * chi S x = ∑ x, g x * chi S (flip x i) := by
    have := Cube.sum_comp_flip i (fun x ↦ g x * chi S (flip x i))
    simp only [flip_flip] at this
    exact this
  unfold fourier
  simp_rw [sub_mul, Finset.sum_sub_distrib, h1, chi_flip]
  by_cases h : i ∈ S
  · simp only [h, ite_true, mul_neg, Finset.sum_neg_distrib]
    ring
  · simp [h]

/-- The energy of direction `i` in the Fourier basis. -/
theorem Cube.sum_sq_sub_flip (g : Cube m → ℝ) (i : Fin m) :
    ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), (g x - g (flip x i)) ^ 2 =
      2 ^ m * ∑ S, if i ∈ S then 2 * fourier g S ^ 2 else 0 := by
  have h := Cube.sum_filter_false_eq_half i (fun x ↦ (g x - g (flip x i)) ^ 2)
    (fun x ↦ by simp only [flip_flip]; ring)
  have h' := sum_sq_eq_sum_fourier (fun x ↦ g x - g (flip x i))
  rw [h, h']
  simp_rw [Cube.fourier_sub_flip]
  rw [mul_div_assoc]
  congr 1
  rw [div_eq_iff two_ne_zero, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  split_ifs <;> ring

/-- **The hypercube Laplacian is diagonal in the characters**, with eigenvalue `2|S|` on `χ_S`. -/
theorem energy_one_eq (g : Cube m → ℝ) :
    energy 1 g = 2 ^ m * ∑ S, 2 * (S.card : ℝ) * fourier g S ^ 2 := by
  unfold energy
  simp only [Pi.one_apply, one_mul]
  simp_rw [Cube.sum_sq_sub_flip]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  simp only [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul]
  ring

theorem energy_nonneg {w : Fin m → Cube m → ℝ} (hw : ∀ i x, 0 ≤ w i x) (g : Cube m → ℝ) :
    0 ≤ energy w g := by
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun x _ ↦ mul_nonneg (hw i x) (sq_nonneg _)

/-- The energies of the low and high parts add up. -/
theorem energy_one_lowProj_add (r : ℕ) (g : Cube m → ℝ) :
    energy 1 (lowProj r g) + energy 1 (g - lowProj r g) = energy 1 g := by
  rw [energy_one_eq, energy_one_eq, energy_one_eq, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [fourier_sub, fourier_lowProj]
  split_ifs <;> ring

/-- Functions with no Fourier mass below degree `r + 1` have energy at least `2 (r + 1)` times
their squared norm. -/
theorem energy_one_high_ge (r : ℕ) (g : Cube m → ℝ) :
    2 * ((r : ℝ) + 1) * ∑ x, (g - lowProj r g) x ^ 2 ≤ energy 1 (g - lowProj r g) := by
  rw [sum_sq_eq_sum_fourier, energy_one_eq]
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum fun S _ ↦ ?_
  have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
  rw [fourier_sub, fourier_lowProj]
  split_ifs with h
  · simp
  · have hc : (r : ℝ) + 1 ≤ S.card := by exact_mod_cast Nat.succ_le_of_lt (not_le.mp h)
    nlinarith [mul_nonneg h2m (sq_nonneg (fourier g S - 0))]

theorem energy_one_le (g : Cube m → ℝ) : energy 1 g ≤ 2 * m * ∑ x, g x ^ 2 := by
  rw [energy_one_eq, sum_sq_eq_sum_fourier]
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum fun S _ ↦ ?_
  have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hc : (S.card : ℝ) ≤ m := by
    have : S.card ≤ m := by simpa using Finset.card_le_univ S
    exact_mod_cast this
  nlinarith [mul_nonneg h2m (sq_nonneg (fourier g S))]

/-- The bilinear form of the Laplacian, edge by edge. -/
theorem Cube.sum_mul_lap_eq (w : Fin m → Cube m → ℝ) (g h : Cube m → ℝ) :
    ∑ x, g x * lap w h x = ∑ i, ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false),
      w i x * ((g x - g (flip x i)) * (h x - h (flip x i))) := by
  unfold lap
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Cube.sum_eq_sum_filter_false i]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' : x i = false := (Finset.mem_filter.1 hx).2
  simp only [lowPt_flip, flip_flip, lowPt_of_false hx']
  ring

/-- The energy is the quadratic form of the Laplacian. -/
theorem sum_mul_lap (w : Fin m → Cube m → ℝ) (g : Cube m → ℝ) :
    ∑ x, g x * lap w g x = energy w g := by
  rw [Cube.sum_mul_lap_eq]
  unfold energy
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  ring

/-- The bilinear form of the Laplacian is symmetric. -/
theorem sum_mul_lap_comm (w : Fin m → Cube m → ℝ) (g h : Cube m → ℝ) :
    ∑ x, g x * lap w h x = ∑ x, h x * lap w g x := by
  rw [Cube.sum_mul_lap_eq, Cube.sum_mul_lap_eq]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  ring

/-- The Laplacian is linear in the weights: `L_{w - p} = L_w - p L_1`. -/
theorem lap_sub_const (w : Fin m → Cube m → ℝ) (p : ℝ) (g : Cube m → ℝ) (x : Cube m) :
    lap (fun i y ↦ w i y - p) g x = lap w g x - p * lap 1 g x := by
  unfold lap
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.one_apply]
  ring

theorem energy_sub_const (w : Fin m → Cube m → ℝ) (p : ℝ) (g : Cube m → ℝ) :
    energy (fun i y ↦ w i y - p) g = energy w g - p * energy 1 g := by
  unfold energy
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [Pi.one_apply]
  ring

/-- The half-cube energy is at most the full one. -/
theorem energy_halfW_le {w : Fin m → Cube m → ℝ} (hw : ∀ i x, 0 ≤ w i x) (i : Fin m)
    (g : Cube m → ℝ) : energy (halfW i w) g ≤ energy w g := by
  unfold energy halfW
  refine Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun x _ ↦ ?_
  split_ifs
  · rw [zero_mul]
    exact mul_nonneg (hw j x) (sq_nonneg _)
  · exact le_rfl

end BMW26
