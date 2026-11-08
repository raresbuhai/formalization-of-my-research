module

public import Background.SumOfSquares.PseudoBounds
public import BS23.Common.Gaussian

/-!
# Analysis of the pseudo-expectation

The deterministic heart of [BS23, Theorem 1.1, §4]: what the pseudo-expectation `Ẽ` found by the
solver says about the sample. It is stated abstractly (`BS23.Separating.PAHyp`), so that it only
uses positivity of `Ẽ` on sums of squares, the bound `|Ẽ f| ≤ ‖f‖₁ R` (E1), the two constraints
on the pair polynomials `F_p = n⁻² ∑_{i,j} L(xᵢ - xⱼ)^p` (E2), and the closeness, in coefficient
`ℓ₁` norm, of the empirical noise moment polynomials `M_c^l = |S_c|⁻¹ ∑_{j ∈ S_c} L(ζⱼ)^l` of each
cluster to the Gaussian ones `G_l = E Z^l · N^(l/2)`. Here `xⱼ = m_{ℓⱼ} + ζⱼ`, `L` is additive of
degree at most `1`, `N` is a sum of squares of degree at most `2`, and `t = r s`.

* **Step 2** (`PAHyp.E_N_pow_le`): `Ẽ N^t ≤ (2/wmin) (2050/t)^t`. The same-cluster terms of
  `F_{2t}` are squares; within a cluster `H^{cc}_{2t} = ∑_l (-1)^l C(2t, l) M_c^l M_c^(2t-l)`
  (`PA.sum_sum_sub_pow_eq_expand`), whose population counterpart is
  `∑_l (-1)^l C(2t, l) G_l G_{2t-l} = 2^t (2t-1)‼ N^t` (`PA.expand_gaussPow`, from the moment
  identity `PA.sum_choose_gaussMom` of the difference of two independent Gaussians), and
  `2^t (2t-1)‼ ≥ t^t` (`PA.pow_le_two_pow_mul_gaussMom`).
* **Step 3** (`PAHyp.E_N_pow_s_le`): `Ẽ N^s ≤ (4100/t)^s`, by Jensen for powers of a sum of
  squares, since `2/wmin ≤ 2^s ≤ 2^t`.
* **Step 4** (`PAHyp.exists_far`): two distinct clusters with `q(m_a - m_b) ≥ 4^(-s)/2`, where
  `q(u) = Ẽ L(u)^(2s)` (`PA.qf`): the pairs of noise vectors of two clusters have
  `∑ q(ζᵢ - ζⱼ) ≤ μ n_a n_b`, `μ = (32800/r)^s + 4^s R e` (`PAHyp.sum_pair_zeta_le`), and
  `Ẽ F_{2s} ≥ 1/2`.
* **Pair fractions** (Markov, `PAHyp.card_near_le`, `PAHyp.card_far_le`): at most
  `δ₁ n_c²` pairs of a cluster have `q(xᵢ - xⱼ) > τ = 1/(4·64^s)`, and at most `δ₁ n_a n_b` pairs
  of `S_a × S_b` have `q(xᵢ - xⱼ) < T = 16^(-s)/2`, with `δ₁ = 4·64^s μ`.
* `PAHyp.rounding_hyps` collects what the rounding step (`BS23/Separating/Rounding.lean`) needs
  for `Q i j = q(xᵢ - xⱼ)`: `Q ≥ 0`, symmetry, the weak triangle inequality
  `Q i j ≤ 2^(2s-1) (Q i p + Q p j)`, `2 · 2^(2s-1) τ < T`, `δ₁ ≤ 10⁻⁴` and the two counts.
-/

@[expose] public section

namespace BS23.Separating

open MvPolynomial Finset SoS

namespace PA

/-! ### Gaussian moments -/

/-- `(2i)! = 2^i i! (2i-1)‼`. -/
theorem factorial_two_mul (i : ℕ) :
    (2 * i).factorial = 2 ^ i * i.factorial * gaussMom (2 * i) := by
  rw [gaussMom, ite_eq_left (even_two_mul i)]
  cases i with
  | zero => simp
  | succ j =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.factorial_eq_mul_doubleFactorial,
      show 2 * j + 1 + 1 = 2 * (j + 1) by ring, Nat.doubleFactorial_two_mul,
      show 2 * (j + 1) - 1 = 2 * j + 1 by omega]

theorem gaussMom_two_mul_add_one (i : ℕ) : gaussMom (2 * i + 1) = 0 := by
  rw [gaussMom, ite_eq_right (Nat.not_even_two_mul_add_one i)]

/-- `C(2t, 2i) (2i-1)‼ (2t-2i-1)‼ = (2t-1)‼ C(t, i)`. -/
theorem choose_mul_gaussMom_mul_gaussMom {i t : ℕ} (hi : i ≤ t) :
    (2 * t).choose (2 * i) * gaussMom (2 * i) * gaussMom (2 * (t - i)) =
      gaussMom (2 * t) * t.choose i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [Nat.add_sub_cancel_left]
  have h1 := Nat.choose_mul_factorial_mul_factorial (show 2 * i ≤ 2 * (i + j) by omega)
  rw [show 2 * (i + j) - 2 * i = 2 * j by omega, factorial_two_mul, factorial_two_mul,
    factorial_two_mul] at h1
  have h2 := Nat.choose_mul_factorial_mul_factorial (show i ≤ i + j by omega)
  rw [Nat.add_sub_cancel_left] at h2
  have hX : 0 < 2 ^ i * 2 ^ j * i.factorial * j.factorial := by positivity
  refine Nat.eq_of_mul_eq_mul_right hX ?_
  calc (2 * (i + j)).choose (2 * i) * gaussMom (2 * i) * gaussMom (2 * j) *
        (2 ^ i * 2 ^ j * i.factorial * j.factorial)
      = (2 * (i + j)).choose (2 * i) * (2 ^ i * i.factorial * gaussMom (2 * i)) *
          (2 ^ j * j.factorial * gaussMom (2 * j)) := by ring
    _ = 2 ^ (i + j) * (i + j).factorial * gaussMom (2 * (i + j)) := h1
    _ = gaussMom (2 * (i + j)) * (i + j).choose i *
          (2 ^ i * 2 ^ j * i.factorial * j.factorial) := by
        rw [← h2]
        ring

/-- **The `2t`-th moment of the difference of two independent standard Gaussians**:
`∑_m (-1)^(m + 2t) C(2t, m) E Z^m E Z^(2t-m) = 2^t (2t-1)‼`. -/
theorem sum_choose_gaussMom (t : ℕ) :
    ∑ m ∈ range (2 * t + 1), (-1 : ℝ) ^ (m + 2 * t) * (2 * t).choose m * gaussMom m *
      gaussMom (2 * t - m) = 2 ^ t * gaussMom (2 * t) := by
  rw [sum_range_two_mul_add_one]
  have hodd : ∀ i ∈ range t, (-1 : ℝ) ^ (2 * i + 1 + 2 * t) * (2 * t).choose (2 * i + 1) *
      gaussMom (2 * i + 1) * gaussMom (2 * t - (2 * i + 1)) = 0 := fun i _ ↦ by
    rw [gaussMom_two_mul_add_one, Nat.cast_zero, mul_zero, zero_mul]
  rw [sum_eq_zero hodd, add_zero]
  have heven : ∀ i ∈ range (t + 1), (-1 : ℝ) ^ (2 * i + 2 * t) * (2 * t).choose (2 * i) *
      gaussMom (2 * i) * gaussMom (2 * t - 2 * i) = gaussMom (2 * t) * t.choose i := fun i hi ↦ by
    have hi : i ≤ t := Nat.lt_succ_iff.1 (mem_range.1 hi)
    rw [show 2 * i + 2 * t = 2 * (i + t) by ring, pow_mul, neg_one_sq, one_pow, one_mul,
      show 2 * t - 2 * i = 2 * (t - i) by omega]
    exact_mod_cast choose_mul_gaussMom_mul_gaussMom hi
  rw [sum_congr rfl heven, ← mul_sum, mul_comm]
  congr 1
  exact_mod_cast Nat.sum_range_choose t

/-- `t^t ≤ 2^t (2t-1)‼`, since `2^t (2t-1)‼ = (2t)!/t! = (t+1) ⋯ (2t)`. -/
theorem pow_le_two_pow_mul_gaussMom (t : ℕ) : t ^ t ≤ 2 ^ t * gaussMom (2 * t) := by
  have h := Nat.factorial_mul_pow_le_factorial (m := t) (n := t)
  rw [← two_mul, factorial_two_mul, mul_comm (2 ^ t), mul_assoc] at h
  exact (Nat.pow_le_pow_left (Nat.le_succ t) t).trans
    (Nat.le_of_mul_le_mul_left h (Nat.factorial_pos t))

/-! ### The polynomials of the analysis -/

variable {σ V : Type*} [AddCommGroup V] {n k : ℕ}

/-- The pair polynomial `F_p = n⁻² ∑_{i,j} L(xᵢ - xⱼ)^p` of the constraints. -/
noncomputable def pairPoly (L : V → MvPolynomial σ ℝ) (x : Fin n → V) (p : ℕ) :
    MvPolynomial σ ℝ :=
  ((n : ℝ) ^ 2)⁻¹ • ∑ i, ∑ j, L (x i - x j) ^ p

/-- The empirical moment polynomial `M_c^l = |S_c|⁻¹ ∑_{j ∈ S_c} L(ζⱼ)^l` of the noise of a
cluster. -/
noncomputable def clusterMom (lab : Fin n → Fin k) (L : V → MvPolynomial σ ℝ) (ζ : Fin n → V)
    (c : Fin k) (l : ℕ) : MvPolynomial σ ℝ :=
  ((cluster lab c).card : ℝ)⁻¹ • ∑ j ∈ cluster lab c, L (ζ j) ^ l

/-- The Gaussian moment polynomial `G_l = E Z^l · N^(l/2)` (zero for odd `l`). -/
noncomputable def gaussPow (N : MvPolynomial σ ℝ) (l : ℕ) : MvPolynomial σ ℝ :=
  (gaussMom l : ℝ) • N ^ (l / 2)

/-- `q(u) = Ẽ L(u)^(2s)`. -/
noncomputable def qf {ℓ : ℕ} (E : PseudoExpectation σ ℓ) (L : V → MvPolynomial σ ℝ) (s : ℕ)
    (u : V) : ℝ :=
  E (L u ^ (2 * s))

/-- The binomial expansion `∑_{l ≤ p} (-1)^(l+p) C(p, l) M_l M_{p-l}` of the `p`-th moment of a
difference of two independent copies, in terms of the moments `M_l`. -/
noncomputable def expand (M : ℕ → MvPolynomial σ ℝ) (p : ℕ) : MvPolynomial σ ℝ :=
  ∑ l ∈ range (p + 1), C ((-1 : ℝ) ^ (l + p) * p.choose l) * (M l * M (p - l))

/-- The bound `μ = (32800/r)^s + 4^s R e` on the pseudo-expected `2s`-th moments of the
differences of noise vectors. -/
noncomputable def mu (r s : ℕ) (R e : ℝ) : ℝ := (32800 / r) ^ s + 4 ^ s * R * e

/-- The fraction `δ₁ = 4 · 64^s · μ` of bad pairs. -/
noncomputable def delta1 (r s : ℕ) (R e : ℝ) : ℝ := 4 * 64 ^ s * ((32800 / r) ^ s + 4 ^ s * R * e)

/-- The threshold `τ = 1/(4 · 64^s)` of the algorithm. -/
noncomputable def tauNear (s : ℕ) : ℝ := 1 / (4 * 64 ^ s)

/-- The threshold `T = 16^(-s)/2` of the analysis. -/
noncomputable def thrFar (s : ℕ) : ℝ := 1 / (2 * 16 ^ s)

/-! ### Expansions -/

/-- `∑_{i, j ∈ S} (Aᵢ - Aⱼ)^p = ∑_{l ≤ p} (-1)^(l+p) C(p, l) (∑ᵢ Aᵢ^l) (∑ⱼ Aⱼ^(p-l))`. -/
theorem sum_sum_sub_pow {ι : Type*} (S : Finset ι) (A : ι → MvPolynomial σ ℝ) (p : ℕ) :
    ∑ i ∈ S, ∑ j ∈ S, (A i - A j) ^ p =
      ∑ l ∈ range (p + 1), C ((-1 : ℝ) ^ (l + p) * p.choose l) *
        ((∑ i ∈ S, A i ^ l) * ∑ j ∈ S, A j ^ (p - l)) := by
  simp_rw [sub_pow, Finset.sum_mul_sum, Finset.mul_sum]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun l _ ↦ sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

/-- The pair sum of a nonempty set, through its empirical moments. -/
theorem sum_sum_sub_pow_eq_expand {ι : Type*} {S : Finset ι} (hS : S.Nonempty)
    (A : ι → MvPolynomial σ ℝ) (p : ℕ) :
    ∑ i ∈ S, ∑ j ∈ S, (A i - A j) ^ p =
      C ((S.card : ℝ) ^ 2) * expand (fun l ↦ (S.card : ℝ)⁻¹ • ∑ i ∈ S, A i ^ l) p := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hY : ∀ l, ∑ i ∈ S, A i ^ l = C (S.card : ℝ) * ((S.card : ℝ)⁻¹ • ∑ i ∈ S, A i ^ l) := by
    intro l
    rw [smul_eq_C_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
  rw [sum_sum_sub_pow, expand, mul_sum]
  refine sum_congr rfl fun l _ ↦ ?_
  conv_lhs => rw [hY l, hY (p - l)]
  rw [map_pow]
  ring

theorem totalDegree_expand_le {M : ℕ → MvPolynomial σ ℝ} {p : ℕ}
    (hM : ∀ l ≤ p, (M l).totalDegree ≤ l) : (expand M p).totalDegree ≤ p := by
  refine totalDegree_finsetSum_le fun l hl ↦ ?_
  have hl : l ≤ p := Nat.lt_succ_iff.1 (mem_range.1 hl)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_mul _ _).trans ?_
  have := hM l hl
  have := hM (p - l) (Nat.sub_le p l)
  omega

/-- `G_m G_(2t-m) = E Z^m E Z^(2t-m) N^t`. -/
theorem gaussPow_mul_gaussPow (N : MvPolynomial σ ℝ) {t l : ℕ} (hl : l ≤ 2 * t) :
    gaussPow N l * gaussPow N (2 * t - l) =
      C ((gaussMom l : ℝ) * gaussMom (2 * t - l)) * N ^ t := by
  rcases Nat.even_or_odd' l with ⟨i, rfl | rfl⟩
  · have hi : i ≤ t := by omega
    rw [gaussPow, gaussPow, show 2 * t - 2 * i = 2 * (t - i) by omega,
      Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos, smul_eq_C_mul,
      smul_eq_C_mul, map_mul]
    calc C (gaussMom (2 * i) : ℝ) * N ^ i * (C (gaussMom (2 * (t - i)) : ℝ) * N ^ (t - i))
        = C (gaussMom (2 * i) : ℝ) * C (gaussMom (2 * (t - i)) : ℝ) * (N ^ i * N ^ (t - i)) := by
          ring
      _ = _ := by rw [← pow_add, Nat.add_sub_cancel' hi]
  · rw [gaussPow, gaussMom_two_mul_add_one, Nat.cast_zero, zero_smul, zero_mul, zero_mul,
      map_zero, zero_mul]

/-- The population counterpart of the pair expansion: `∑_l (-1)^l C(2t, l) G_l G_{2t-l} =
2^t (2t-1)‼ N^t`. -/
theorem expand_gaussPow (N : MvPolynomial σ ℝ) (t : ℕ) :
    expand (gaussPow N) (2 * t) = C (2 ^ t * (gaussMom (2 * t) : ℝ)) * N ^ t := by
  rw [expand, ← sum_choose_gaussMom, map_sum, sum_mul]
  refine sum_congr rfl fun l hl ↦ ?_
  rw [gaussPow_mul_gaussPow N (Nat.lt_succ_iff.1 (mem_range.1 hl))]
  simp only [map_mul]
  ring

/-- `‖a b - a' b'‖₁ ≤ 3 G e` when `‖a - a'‖₁, ‖b - b'‖₁ ≤ e ≤ G` and `‖a'‖₁, ‖b'‖₁ ≤ G`. -/
theorem coeffNorm1_mul_sub_mul_le {a b a' b' : MvPolynomial σ ℝ} {e G : ℝ}
    (ha : coeffNorm1 (a - a') ≤ e) (hb : coeffNorm1 (b - b') ≤ e) (ha' : coeffNorm1 a' ≤ G)
    (hb' : coeffNorm1 b' ≤ G) (heG : e ≤ G) : coeffNorm1 (a * b - a' * b') ≤ 3 * G * e := by
  have he : 0 ≤ e := (coeffNorm1_nonneg _).trans ha
  have hb2 : coeffNorm1 b ≤ e + G := by
    calc coeffNorm1 b = coeffNorm1 ((b - b') + b') := by rw [sub_add_cancel]
      _ ≤ coeffNorm1 (b - b') + coeffNorm1 b' := coeffNorm1_add_le _ _
      _ ≤ e + G := add_le_add hb hb'
  have hsplit : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [hsplit]
  calc coeffNorm1 ((a - a') * b + a' * (b - b'))
      ≤ coeffNorm1 (a - a') * coeffNorm1 b + coeffNorm1 a' * coeffNorm1 (b - b') :=
        (coeffNorm1_add_le _ _).trans (add_le_add (coeffNorm1_mul_le _ _) (coeffNorm1_mul_le _ _))
    _ ≤ e * (e + G) + G * e :=
        add_le_add (mul_le_mul ha hb2 (coeffNorm1_nonneg _) he)
          (mul_le_mul ha' hb (coeffNorm1_nonneg _) (he.trans heG))
    _ ≤ 3 * G * e := by nlinarith

/-- The expansions of close moment sequences are close: `‖expand M p - expand G p‖₁ ≤
2^p · 3 G e`. -/
theorem coeffNorm1_expand_sub_le {M G : ℕ → MvPolynomial σ ℝ} {p : ℕ} {e Gst : ℝ}
    (hM : ∀ l ≤ p, coeffNorm1 (M l - G l) ≤ e) (hG : ∀ l ≤ p, coeffNorm1 (G l) ≤ Gst)
    (heG : e ≤ Gst) : coeffNorm1 (expand M p - expand G p) ≤ 2 ^ p * (3 * Gst * e) := by
  rw [expand, expand, ← sum_sub_distrib]
  refine (coeffNorm1_sum_le _ _).trans ?_
  have h2 : (2 : ℝ) ^ p = ∑ l ∈ range (p + 1), (p.choose l : ℝ) := by
    exact_mod_cast (Nat.sum_range_choose p).symm
  rw [h2, sum_mul]
  refine sum_le_sum fun l hl ↦ ?_
  have hl : l ≤ p := Nat.lt_succ_iff.1 (mem_range.1 hl)
  rw [← mul_sub, coeffNorm1_C_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left (coeffNorm1_mul_sub_mul_le (hM l hl) (hM _ (Nat.sub_le p l))
    (hG l hl) (hG _ (Nat.sub_le p l)) heG) (Nat.cast_nonneg _)

/-! ### Sums over clusters -/

theorem sum_univ_eq_sum_cluster {M : Type*} [AddCommMonoid M] (lab : Fin n → Fin k)
    (f : Fin n → M) : ∑ i, f i = ∑ c, ∑ i ∈ cluster lab c, f i :=
  (Finset.sum_fiberwise univ lab f).symm

theorem sum_sum_eq_sum_cluster (lab : Fin n → Fin k) (f : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, f i j = ∑ a, ∑ b, ∑ i ∈ cluster lab a, ∑ j ∈ cluster lab b, f i j := by
  rw [sum_univ_eq_sum_cluster lab (fun i ↦ ∑ j, f i j)]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_comm, sum_univ_eq_sum_cluster lab (fun j ↦ ∑ i ∈ cluster lab a, f i j)]
  exact sum_congr rfl fun b _ ↦ Finset.sum_comm

theorem sum_cluster_le_sum_sum (lab : Fin n → Fin k) (f : Fin n → Fin n → ℝ)
    (hf : ∀ i j, 0 ≤ f i j) :
    ∑ c, ∑ i ∈ cluster lab c, ∑ j ∈ cluster lab c, f i j ≤ ∑ i, ∑ j, f i j := by
  rw [sum_sum_eq_sum_cluster lab]
  refine sum_le_sum fun a _ ↦ ?_
  exact single_le_sum (f := fun b ↦ ∑ i ∈ cluster lab a, ∑ j ∈ cluster lab b, f i j)
    (fun b _ ↦ sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ hf i j) (mem_univ a)

theorem sum_card_cluster (lab : Fin n → Fin k) : ∑ c, ((cluster lab c).card : ℝ) = n := by
  have h := sum_univ_eq_sum_cluster lab (fun _ ↦ (1 : ℝ))
  simpa using h.symm

theorem card_cluster_le (lab : Fin n → Fin k) (c : Fin k) : ((cluster lab c).card : ℝ) ≤ n := by
  have : (cluster lab c).card ≤ n := (card_filter_le _ _).trans (by simp)
  exact_mod_cast this

theorem lab_of_mem_cluster {lab : Fin n → Fin k} {c : Fin k} {i : Fin n}
    (hi : i ∈ cluster lab c) : lab i = c :=
  (mem_filter.1 hi).2

theorem sum_sq_card_cluster_le (lab : Fin n → Fin k) :
    ∑ c, ((cluster lab c).card : ℝ) ^ 2 ≤ n ^ 2 :=
  calc ∑ c, ((cluster lab c).card : ℝ) ^ 2 ≤ ∑ c, ((cluster lab c).card : ℝ) * n :=
        sum_le_sum fun c _ ↦ by
          rw [sq]
          exact mul_le_mul_of_nonneg_left (card_cluster_le lab c) (Nat.cast_nonneg _)
    _ = n ^ 2 := by rw [← sum_mul, sum_card_cluster, sq]

/-- **Markov**: at most `(∑ f)/θ` elements have `f > θ`, for `f ≥ 0`. -/
theorem card_filter_lt_le {ι : Type*} (P : Finset ι) (f : ι → ℝ) (hf : ∀ p ∈ P, 0 ≤ f p)
    {θ : ℝ} (hθ : 0 < θ) : ((P.filter fun p ↦ θ < f p).card : ℝ) ≤ (∑ p ∈ P, f p) / θ := by
  rw [le_div_iff₀ hθ]
  have h1 := card_nsmul_le_sum (P.filter fun p ↦ θ < f p) f θ fun p hp ↦ (mem_filter.1 hp).2.le
  rw [nsmul_eq_mul] at h1
  exact h1.trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p hp _ ↦ hf p hp)

theorem E_pairPoly {ℓ : ℕ} (E : PseudoExpectation σ ℓ) (L : V → MvPolynomial σ ℝ)
    (x : Fin n → V) (p : ℕ) :
    E (pairPoly L x p) = ((n : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, E (L (x i - x j) ^ p) := by
  rw [pairPoly, E.map_smul, E.map_sum]
  simp_rw [E.map_sum]

theorem gaussPow_zero (N : MvPolynomial σ ℝ) : gaussPow N 0 = 1 := by
  simp [gaussPow, gaussMom]

omit [AddCommGroup V] in
theorem totalDegree_clusterMom_le {L : V → MvPolynomial σ ℝ}
    (hL : ∀ u, (L u).totalDegree ≤ 1) (lab : Fin n → Fin k) (ζ : Fin n → V) (c : Fin k)
    (l : ℕ) : (clusterMom lab L ζ c l).totalDegree ≤ l :=
  (totalDegree_smul_le _ _).trans (totalDegree_finsetSum_le fun _ _ ↦
    (totalDegree_pow _ _).trans ((Nat.mul_le_mul_left l (hL _)).trans (mul_one l).le))

theorem totalDegree_gaussPow_le {N : MvPolynomial σ ℝ} (hN : N.totalDegree ≤ 2) (l : ℕ) :
    (gaussPow N l).totalDegree ≤ l :=
  (totalDegree_smul_le _ _).trans ((totalDegree_pow _ _).trans
    ((Nat.mul_le_mul_left _ hN).trans (Nat.div_mul_le_self l 2)))

/-- `16^s = (4^s)²`. -/
theorem sixteen_pow (s : ℕ) : (16 : ℝ) ^ s = (4 ^ s) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- `64^s = (4^s)³`. -/
theorem sixtyfour_pow (s : ℕ) : (64 : ℝ) ^ s = (4 ^ s) ^ 3 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- `2^(2s-1) · 2 = 4^s` for `s ≥ 1`. -/
theorem two_pow_mul_two {s : ℕ} (hs : 1 ≤ s) : (2 : ℝ) ^ (2 * s - 1) * 2 = 4 ^ s := by
  rw [← pow_succ, Nat.sub_add_cancel (by omega), pow_mul]
  norm_num

theorem delta1_eq (r s : ℕ) (R e : ℝ) : delta1 r s R e = 4 * 64 ^ s * mu r s R e := rfl

theorem tauNear_pos (s : ℕ) : 0 < tauNear s := by
  rw [tauNear]
  positivity

theorem thrFar_pos (s : ℕ) : 0 < thrFar s := by
  rw [thrFar]
  positivity

/-- The thresholds fit the weak triangle inequality: `2 · 2^(2s-1) · τ = 16^(-s)/4 < T`. -/
theorem two_mul_two_pow_mul_tauNear_lt {s : ℕ} (hs : 1 ≤ s) :
    2 * 2 ^ (2 * s - 1) * tauNear s < thrFar s := by
  rw [mul_comm 2, two_pow_mul_two hs, tauNear, thrFar, sixtyfour_pow, sixteen_pow]
  have hu : (0 : ℝ) < 4 ^ s := by positivity
  set u : ℝ := 4 ^ s
  rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos hu 3]

end PA

/-! ### The hypotheses -/

/-- **The data and hypotheses of the analysis of the pseudo-expectation** [BS23, §4], in an
abstract setting. Points `xⱼ = m_{ℓⱼ} + ζⱼ` in an additive group `V`, with labels
`lab : Fin n → Fin k` (clusters `S_c = cluster lab c` of sizes `n_c ≥ (wmin/2) n`), are turned into
polynomials by an additive map `L` of degree at most `1` (later `L u = ⟨u, X⟩`). `E` is a
pseudo-expectation of degree `ℓ ≥ 2t`, `t = r s`, with `|Ẽ f| ≤ ‖f‖₁ R` for `deg f ≤ 2t` (E1)
and the two constraints `Ẽ F_{2s} ≥ 1/2`, `Ẽ F_{2t} ≤ 1024^t + 1/2` (E2), where
`F_p = n⁻² ∑_{i,j} L(xᵢ - xⱼ)^p`. `N` is a sum of squares of degree at most `2` and the
empirical noise moments `M_c^l = |S_c|⁻¹ ∑_{j ∈ S_c} L(ζⱼ)^l` of each cluster are within `e`, in
`‖·‖₁`, of the Gaussian ones `G_l = E Z^l · N^(l/2)`, which have `‖G_l‖₁ ≤ Gst` (`l ≤ 2t`).
The last two fields are the smallness assumptions `R · 3 · 4^t · Gst · e ≤ 1/2` and
`δ₁ = 4 · 64^s ((32800/r)^s + 4^s R e) ≤ 10⁻⁴`. -/
structure PAHyp {σ V : Type*} [AddCommGroup V] {n k : ℕ} (lab : Fin n → Fin k)
    (x : Fin n → V) (m : Fin k → V) (ζ : Fin n → V) (L : V → MvPolynomial σ ℝ) (r s t : ℕ)
    {ℓ : ℕ} (E : PseudoExpectation σ ℓ) (N : MvPolynomial σ ℝ) (wmin R e Gst : ℝ) : Prop where
  x_eq : ∀ j, x j = m (lab j) + ζ j
  L_add : ∀ u v, L (u + v) = L u + L v
  L_neg : ∀ u, L (-u) = -L u
  totalDegree_L_le : ∀ u, (L u).totalDegree ≤ 1
  one_le_r : 1 ≤ r
  one_le_s : 1 ≤ s
  t_eq : t = r * s
  two_mul_t_le : 2 * t ≤ ℓ
  abs_E_le : ∀ f : MvPolynomial σ ℝ, f.totalDegree ≤ 2 * t → |E f| ≤ coeffNorm1 f * R
  E_pair_lower : 1 / 2 ≤ E (PA.pairPoly L x (2 * s))
  E_pair_upper : E (PA.pairPoly L x (2 * t)) ≤ 1024 ^ t + 1 / 2
  N_isSumSq : IsSumSq N
  totalDegree_N_le : N.totalDegree ≤ 2
  mom_close : ∀ c l, l ≤ 2 * t → coeffNorm1 (PA.clusterMom lab L ζ c l - PA.gaussPow N l) ≤ e
  gauss_le : ∀ l, l ≤ 2 * t → coeffNorm1 (PA.gaussPow N l) ≤ Gst
  n_pos : 0 < n
  wmin_pos : 0 < wmin
  one_le_wmin_mul : 1 ≤ wmin * 2 ^ (s - 1)
  card_ge : ∀ c, wmin / 2 * n ≤ (cluster lab c).card
  small_e : R * (3 * 4 ^ t * Gst * e) ≤ 1 / 2
  small_delta : 4 * 64 ^ s * ((32800 / r) ^ s + 4 ^ s * R * e) ≤ 1 / 10000

namespace PAHyp

open PA

variable {σ V : Type*} [AddCommGroup V] {n k : ℕ} {lab : Fin n → Fin k} {x : Fin n → V}
  {m : Fin k → V} {ζ : Fin n → V} {L : V → MvPolynomial σ ℝ} {r s t ℓ : ℕ}
  {E : PseudoExpectation σ ℓ} {N : MvPolynomial σ ℝ} {wmin R e Gst : ℝ}
  (h : PAHyp lab x m ζ L r s t E N wmin R e Gst)
include h

/-! #### Basic consequences -/

theorem L_zero : L 0 = 0 := by simpa using h.L_add 0 0

theorem L_sub (u v : V) : L (u - v) = L u - L v := by
  rw [sub_eq_add_neg, h.L_add, h.L_neg, ← sub_eq_add_neg]

theorem s_le_t : s ≤ t := by
  rw [h.t_eq]
  exact Nat.le_mul_of_pos_left s h.one_le_r

theorem one_le_t : 1 ≤ t := h.one_le_s.trans h.s_le_t

theorem two_mul_s_le : 2 * s ≤ ℓ := (Nat.mul_le_mul_left 2 h.s_le_t).trans h.two_mul_t_le

theorem one_le_R : 1 ≤ R := by
  have := h.abs_E_le 1 (by simp)
  rwa [E.map_one, abs_one, coeffNorm1_one, one_mul] at this

theorem one_le_Gst : 1 ≤ Gst := by
  have := h.gauss_le 0 (Nat.zero_le _)
  rwa [gaussPow_zero, coeffNorm1_one] at this

theorem e_nonneg : 0 ≤ e :=
  (coeffNorm1_nonneg _).trans (h.mom_close (lab ⟨0, h.n_pos⟩) 0 (Nat.zero_le _))

theorem e_le_Gst : e ≤ Gst := by
  have hR := h.one_le_R
  have hG := h.one_le_Gst
  have he := h.e_nonneg
  have h4 : (1 : ℝ) ≤ 4 ^ t := one_le_pow₀ (by norm_num)
  have hX : 0 ≤ 3 * 4 ^ t * Gst * e := by
    have : (0 : ℝ) ≤ 4 ^ t := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) this) (by linarith)) he
  have h1 : 3 * 4 ^ t * Gst * e ≤ 1 / 2 := (le_mul_of_one_le_left hX hR).trans h.small_e
  have h2 : e ≤ 3 * 4 ^ t * Gst * e :=
    le_mul_of_one_le_left he (by nlinarith)
  linarith

theorem n_pos' : (0 : ℝ) < n := by exact_mod_cast h.n_pos

theorem card_pos (c : Fin k) : (0 : ℝ) < (cluster lab c).card := by
  have := h.wmin_pos
  have := h.n_pos'
  exact lt_of_lt_of_le (by positivity) (h.card_ge c)

theorem cluster_nonempty (c : Fin k) : (cluster lab c).Nonempty :=
  Finset.card_pos.1 (by exact_mod_cast h.card_pos c)

theorem sum_sq_card_ge : wmin / 2 * n ^ 2 ≤ ∑ c, ((cluster lab c).card : ℝ) ^ 2 :=
  calc wmin / 2 * n ^ 2 = ∑ c, ((cluster lab c).card : ℝ) * (wmin / 2 * n) := by
        rw [← sum_mul, sum_card_cluster]
        ring
    _ ≤ ∑ c, ((cluster lab c).card : ℝ) ^ 2 := sum_le_sum fun c _ ↦ by
        rw [sq]
        exact mul_le_mul_of_nonneg_left (h.card_ge c) (Nat.cast_nonneg _)

/-- Within a cluster, `xᵢ - xⱼ = ζᵢ - ζⱼ`. -/
theorem x_sub_of_mem_same {c : Fin k} {i j : Fin n} (hi : i ∈ cluster lab c)
    (hj : j ∈ cluster lab c) : x i - x j = ζ i - ζ j := by
  rw [h.x_eq i, h.x_eq j, lab_of_mem_cluster hi, lab_of_mem_cluster hj, add_sub_add_left_eq_sub]

/-- Between clusters, `xᵢ - xⱼ = (m_a - m_b) + (ζᵢ - ζⱼ)`. -/
theorem x_sub_of_mem {a b : Fin k} {i j : Fin n} (hi : i ∈ cluster lab a)
    (hj : j ∈ cluster lab b) : x i - x j = (m a - m b) + (ζ i - ζ j) := by
  rw [h.x_eq i, h.x_eq j, lab_of_mem_cluster hi, lab_of_mem_cluster hj]
  abel

/-! #### The quadratic-like form `q` -/

theorem qf_nonneg (u : V) : 0 ≤ qf E L s u :=
  E.apply_pow_two_mul_nonneg (h.totalDegree_L_le u) (by rw [mul_one]; exact h.two_mul_s_le)

theorem qf_neg (u : V) : qf E L s (-u) = qf E L s u := by
  rw [qf, qf, h.L_neg, (even_two_mul s).neg_pow]

theorem qf_zero : qf E L s 0 = 0 := by
  rw [qf, h.L_zero, zero_pow (by have := h.one_le_s; omega), E.map_zero]

theorem qf_sub_comm (u v : V) : qf E L s (u - v) = qf E L s (v - u) := by
  rw [← neg_sub, h.qf_neg]

/-- **Weak triangle inequality** for `q`. -/
theorem qf_add_le (u v : V) :
    qf E L s (u + v) ≤ 2 ^ (2 * s - 1) * (qf E L s u + qf E L s v) := by
  rw [qf, h.L_add]
  exact E.apply_add_pow_le_of_totalDegree_le_one (h.totalDegree_L_le u) (h.totalDegree_L_le v)
    h.two_mul_s_le

theorem qf_sub_le (u v : V) :
    qf E L s (u - v) ≤ 2 ^ (2 * s - 1) * (qf E L s u + qf E L s v) := by
  rw [sub_eq_add_neg, ← h.qf_neg v]
  exact h.qf_add_le u (-v)

theorem E_N_pow_nonneg {j : ℕ} (hj : 2 * j ≤ ℓ) : 0 ≤ E (N ^ j) :=
  E.nonneg_of_isSumSq (isSumSq_pow h.N_isSumSq j) ((totalDegree_pow _ _).trans
    ((Nat.mul_le_mul_left j h.totalDegree_N_le).trans (by rw [mul_comm]; exact hj)))

theorem E_pow_nonneg (u : V) {p : ℕ} (hp : 2 * p ≤ ℓ) : 0 ≤ E (L u ^ (2 * p)) :=
  E.apply_pow_two_mul_nonneg (h.totalDegree_L_le u) (by rw [mul_one]; exact hp)

/-! #### Step 2: `Ẽ N^t ≤ (2/wmin) (2050/t)^t` -/

/-- The pair sum of a cluster, through the empirical moments of its noise. -/
theorem sum_same_eq (c : Fin k) (p : ℕ) :
    ∑ i ∈ cluster lab c, ∑ j ∈ cluster lab c, E (L (x i - x j) ^ p) =
      ((cluster lab c).card : ℝ) ^ 2 * E (expand (clusterMom lab L ζ c) p) := by
  calc ∑ i ∈ cluster lab c, ∑ j ∈ cluster lab c, E (L (x i - x j) ^ p)
      = E (∑ i ∈ cluster lab c, ∑ j ∈ cluster lab c, (L (ζ i) - L (ζ j)) ^ p) := by
        rw [E.map_sum]
        refine sum_congr rfl fun i hi ↦ ?_
        rw [E.map_sum]
        refine sum_congr rfl fun j hj ↦ ?_
        rw [h.x_sub_of_mem_same hi hj, h.L_sub]
    _ = _ := by
        rw [sum_sum_sub_pow_eq_expand (h.cluster_nonempty c) (fun j ↦ L (ζ j)) p, E.map_C_mul]
        rfl

/-- `Ẽ H^{cc}_{2t} ≥ 2^t (2t-1)‼ Ẽ N^t - 1/2`: the empirical expansion is within `3·4^t·Gst·e` of
the population one, in `‖·‖₁`. -/
theorem E_expand_ge (c : Fin k) :
    2 ^ t * (gaussMom (2 * t) : ℝ) * E (N ^ t) - 1 / 2 ≤
      E (expand (clusterMom lab L ζ c) (2 * t)) := by
  have hdiff := coeffNorm1_expand_sub_le (p := 2 * t) (fun l hl ↦ h.mom_close c l hl)
    (fun l hl ↦ h.gauss_le l hl) h.e_le_Gst
  rw [expand_gaussPow] at hdiff
  have hdeg : (expand (clusterMom lab L ζ c) (2 * t) -
      C (2 ^ t * (gaussMom (2 * t) : ℝ)) * N ^ t).totalDegree ≤ 2 * t := by
    refine (totalDegree_sub _ _).trans (max_le (totalDegree_expand_le fun l _ ↦
      totalDegree_clusterMom_le h.totalDegree_L_le lab ζ c l) ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add, mul_comm 2 t]
    exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left t h.totalDegree_N_le)
  have habs := h.abs_E_le _ hdeg
  rw [E.map_sub, E.map_C_mul] at habs
  have hR : 0 ≤ R := zero_le_one.trans h.one_le_R
  have h4 : (2 : ℝ) ^ (2 * t) = 4 ^ t := by rw [pow_mul]; norm_num
  have hsm : coeffNorm1 (expand (clusterMom lab L ζ c) (2 * t) -
      C (2 ^ t * (gaussMom (2 * t) : ℝ)) * N ^ t) * R ≤ 1 / 2 :=
    calc _ ≤ 2 ^ (2 * t) * (3 * Gst * e) * R := mul_le_mul_of_nonneg_right hdiff hR
      _ = R * (3 * 4 ^ t * Gst * e) := by rw [h4]; ring
      _ ≤ 1 / 2 := h.small_e
  linarith [(abs_le.1 (habs.trans hsm)).1]

/-- `1024^t + 1 ≤ 2050^t` for `t ≥ 1`. -/
theorem pow_add_one_le : (1024 : ℝ) ^ t + 1 ≤ 2050 ^ t := by
  have h1 : (1 : ℝ) ≤ 1024 ^ t := one_le_pow₀ (by norm_num)
  have h2 : (2 : ℝ) ≤ 2 ^ t :=
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) h.one_le_t
  have h3 : (2 : ℝ) ^ t * 1024 ^ t ≤ 2050 ^ t := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) t
  nlinarith

/-- **Step 2**: `Ẽ N^t ≤ (2/wmin) (2050/t)^t`. The same-cluster terms of `F_{2t}` are squares and
`Ẽ H^{cc}_{2t} ≥ 2^t (2t-1)‼ Ẽ N^t - 1/2`, with `2^t (2t-1)‼ ≥ t^t`. -/
theorem E_N_pow_le : E (N ^ t) ≤ 2 / wmin * (2050 / t) ^ t := by
  set κ : ℝ := 2 ^ t * (gaussMom (2 * t) : ℝ) with hκ
  set X := E (N ^ t) with hXdef
  have hX : 0 ≤ X := h.E_N_pow_nonneg h.two_mul_t_le
  have hn := h.n_pos'
  have hw := h.wmin_pos
  have ht : (0 : ℝ) < t := by exact_mod_cast h.one_le_t
  have hκt : (t : ℝ) ^ t ≤ κ := by
    rw [hκ]
    exact_mod_cast pow_le_two_pow_mul_gaussMom t
  -- The constraint, multiplied by `n²`.
  have hF : ∑ i, ∑ j, E (L (x i - x j) ^ (2 * t)) ≤ n ^ 2 * (1024 ^ t + 1 / 2) := by
    have := h.E_pair_upper
    rw [E_pairPoly, inv_mul_le_iff₀ (by positivity)] at this
    exact this
  -- Keep the same-cluster pairs.
  have hlow : ∑ c, ((cluster lab c).card : ℝ) ^ 2 * (κ * X - 1 / 2) ≤
      ∑ i, ∑ j, E (L (x i - x j) ^ (2 * t)) :=
    calc ∑ c, ((cluster lab c).card : ℝ) ^ 2 * (κ * X - 1 / 2)
        ≤ ∑ c, ∑ i ∈ cluster lab c, ∑ j ∈ cluster lab c, E (L (x i - x j) ^ (2 * t)) :=
          sum_le_sum fun c _ ↦ by
            rw [h.sum_same_eq c]
            exact mul_le_mul_of_nonneg_left (h.E_expand_ge c) (sq_nonneg _)
      _ ≤ _ := sum_cluster_le_sum_sum lab _ fun i j ↦ h.E_pow_nonneg _ h.two_mul_t_le
  rw [← sum_mul] at hlow
  have hS1 := h.sum_sq_card_ge
  have hS2 := sum_sq_card_cluster_le lab
  have hκX : 0 ≤ κ * X := mul_nonneg (by positivity) hX
  -- `(wmin/2) κ X ≤ 1024^t + 1`.
  have hmain : wmin / 2 * (κ * X) ≤ 1024 ^ t + 1 := by
    have h1 : wmin / 2 * n ^ 2 * (κ * X) - n ^ 2 / 2 ≤
        (∑ c, ((cluster lab c).card : ℝ) ^ 2) * (κ * X - 1 / 2) := by
      nlinarith
    have h2 : n ^ 2 * (wmin / 2 * (κ * X)) ≤ n ^ 2 * (1024 ^ t + 1) := by nlinarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  have hmain' : X * (wmin / 2 * (t : ℝ) ^ t) ≤ 2050 ^ t := by
    have := h.pow_add_one_le
    have : wmin / 2 * ((t : ℝ) ^ t * X) ≤ wmin / 2 * (κ * X) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hκt hX) (by positivity)
    nlinarith
  rw [div_pow, show 2 / wmin * ((2050 : ℝ) ^ t / (t : ℝ) ^ t) =
    2050 ^ t / (wmin / 2 * (t : ℝ) ^ t) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  exact hmain'

/-! #### Step 3: `Ẽ N^s ≤ (4100/t)^s` -/

theorem two_div_wmin_le : 2 / wmin ≤ 2 ^ t := by
  have hw := h.wmin_pos
  have h1 := h.one_le_wmin_mul
  rw [div_le_iff₀ hw]
  calc (2 : ℝ) ≤ wmin * 2 ^ (s - 1) * 2 := by linarith
    _ = wmin * 2 ^ s := by rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel h.one_le_s]
    _ ≤ wmin * 2 ^ t := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) h.s_le_t) hw.le
    _ = 2 ^ t * wmin := mul_comm _ _

/-- **Step 3**: `Ẽ N^s ≤ (4100/t)^s`, from `Ẽ N^t ≤ (4100/t)^t` (Step 2 and `2/wmin ≤ 2^t`) by
Jensen for powers of a sum of squares. -/
theorem E_N_pow_s_le : E (N ^ s) ≤ (4100 / t) ^ s := by
  have ht : (0 : ℝ) < t := by exact_mod_cast h.one_le_t
  have hEt : E (N ^ (r * s)) ≤ (4100 / t) ^ (r * s) := by
    rw [← h.t_eq]
    calc E (N ^ t) ≤ 2 / wmin * (2050 / t) ^ t := h.E_N_pow_le
      _ ≤ 2 ^ t * (2050 / t) ^ t := mul_le_mul_of_nonneg_right h.two_div_wmin_le (by positivity)
      _ = (4100 / t) ^ t := by
          rw [← mul_pow]
          congr 1
          ring
  exact E.apply_pow_le_of_apply_pow_mul_le h.N_isSumSq h.totalDegree_N_le h.one_le_r
    (by rw [← h.t_eq, mul_comm]; exact h.two_mul_t_le) (by positivity) hEt

/-! #### Step 4: two far apart cluster centers -/

/-- `Ẽ M_c^{2s} ≤ (2s)^s (4100/t)^s + R e`. -/
theorem E_clusterMom_le (c : Fin k) :
    E (clusterMom lab L ζ c (2 * s)) ≤ (2 * s) ^ s * (4100 / t) ^ s + R * e := by
  have hst : 2 * s ≤ 2 * t := Nat.mul_le_mul_left 2 h.s_le_t
  have hdeg : (clusterMom lab L ζ c (2 * s) - gaussPow N (2 * s)).totalDegree ≤ 2 * t :=
    (totalDegree_sub _ _).trans (max_le
      ((totalDegree_clusterMom_le h.totalDegree_L_le lab ζ c _).trans hst)
      ((totalDegree_gaussPow_le h.totalDegree_N_le _).trans hst))
  have habs := h.abs_E_le _ hdeg
  have hmc := h.mom_close c (2 * s) hst
  rw [E.map_sub] at habs
  have hG : E (gaussPow N (2 * s)) = (gaussMom (2 * s) : ℝ) * E (N ^ s) := by
    rw [gaussPow, E.map_smul, Nat.mul_div_cancel_left s two_pos]
  have hgm : (gaussMom (2 * s) : ℝ) ≤ (2 * s) ^ s := by exact_mod_cast gaussMom_two_mul_le s
  have hNs := h.E_N_pow_s_le
  have hNs0 : 0 ≤ E (N ^ s) := h.E_N_pow_nonneg h.two_mul_s_le
  have hR : 0 ≤ R := zero_le_one.trans h.one_le_R
  have ht : (0 : ℝ) < t := by exact_mod_cast h.one_le_t
  calc E (clusterMom lab L ζ c (2 * s))
      = E (gaussPow N (2 * s)) +
          (E (clusterMom lab L ζ c (2 * s)) - E (gaussPow N (2 * s))) := by ring
    _ ≤ (gaussMom (2 * s) : ℝ) * E (N ^ s) +
          coeffNorm1 (clusterMom lab L ζ c (2 * s) - gaussPow N (2 * s)) * R :=
        add_le_add hG.le ((le_abs_self _).trans habs)
    _ ≤ (2 * s) ^ s * (4100 / t) ^ s + e * R :=
        add_le_add (mul_le_mul hgm hNs hNs0 (by positivity)) (mul_le_mul_of_nonneg_right hmc hR)
    _ = _ := by ring

/-- `∑_{i ∈ S_c} q(ζᵢ) = n_c Ẽ M_c^{2s} ≤ n_c ((2s)^s (4100/t)^s + R e)`. -/
theorem sum_qf_le (c : Fin k) :
    ∑ i ∈ cluster lab c, qf E L s (ζ i) ≤
      ((cluster lab c).card : ℝ) * ((2 * s) ^ s * (4100 / t) ^ s + R * e) := by
  have : ∑ i ∈ cluster lab c, qf E L s (ζ i) =
      ((cluster lab c).card : ℝ) * E (clusterMom lab L ζ c (2 * s)) := by
    rw [clusterMom, E.map_smul, ← mul_assoc, mul_inv_cancel₀ (h.card_pos c).ne', one_mul,
      E.map_sum]
    rfl
  rw [this]
  exact mul_le_mul_of_nonneg_left (h.E_clusterMom_le c) (h.card_pos c).le

theorem mu_eq : mu r s R e = 4 ^ s * ((2 * s) ^ s * (4100 / t) ^ s + R * e) := by
  have hr : (r : ℝ) ≠ 0 := by have := h.one_le_r; positivity
  have hs : (s : ℝ) ≠ 0 := by have := h.one_le_s; positivity
  rw [mu, mul_add, ← mul_pow, ← mul_pow, h.t_eq, Nat.cast_mul]
  congr 1
  · congr 1
    field_simp
    ring
  · ring

theorem mu_nonneg : 0 ≤ mu r s R e := by
  have hR : 0 ≤ R := zero_le_one.trans h.one_le_R
  have he := h.e_nonneg
  rw [mu]
  positivity

/-- `μ < 4^(-s)/2`, from `δ₁ ≤ 10⁻⁴`. -/
theorem mu_lt : mu r s R e < (4 ^ s : ℝ)⁻¹ / 2 := by
  have hmu := h.mu_nonneg
  have hd := h.small_delta
  rw [← mu, sixtyfour_pow] at hd
  have hu : (4 : ℝ) ≤ 4 ^ s :=
    calc (4 : ℝ) = 4 ^ 1 := (pow_one 4).symm
      _ ≤ 4 ^ s := pow_le_pow_right₀ (by norm_num) h.one_le_s
  set u : ℝ := 4 ^ s
  have hu0 : 0 < u := by linarith
  rw [lt_div_iff₀ two_pos, ← one_div, lt_div_iff₀ hu0]
  have hu3 : u ≤ u ^ 3 :=
    calc u = u * 1 := (mul_one u).symm
      _ ≤ u * u ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hu0.le
      _ = u ^ 3 := by ring
  have : mu r s R e * u ≤ mu r s R e * u ^ 3 := mul_le_mul_of_nonneg_left hu3 hmu
  linarith

/-- The pairs of noise vectors of two clusters: `∑_{i ∈ S_a, j ∈ S_b} q(ζᵢ - ζⱼ) ≤ μ n_a n_b`. -/
theorem sum_pair_zeta_le (a b : Fin k) :
    ∑ i ∈ cluster lab a, ∑ j ∈ cluster lab b, qf E L s (ζ i - ζ j) ≤
      mu r s R e * (cluster lab a).card * (cluster lab b).card := by
  set K : ℝ := 2 ^ (2 * s - 1) with hK
  set β : ℝ := (2 * s) ^ s * (4100 / t) ^ s + R * e with hβ
  have hK0 : 0 ≤ K := by positivity
  calc ∑ i ∈ cluster lab a, ∑ j ∈ cluster lab b, qf E L s (ζ i - ζ j)
      ≤ ∑ i ∈ cluster lab a, ∑ j ∈ cluster lab b, K * (qf E L s (ζ i) + qf E L s (ζ j)) :=
        sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ h.qf_sub_le _ _
    _ = K * (((cluster lab b).card : ℝ) * ∑ i ∈ cluster lab a, qf E L s (ζ i) +
          ((cluster lab a).card : ℝ) * ∑ j ∈ cluster lab b, qf E L s (ζ j)) := by
        simp_rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    _ ≤ K * (((cluster lab b).card : ℝ) * (((cluster lab a).card : ℝ) * β) +
          ((cluster lab a).card : ℝ) * (((cluster lab b).card : ℝ) * β)) := by
        gcongr
        · exact h.sum_qf_le a
        · exact h.sum_qf_le b
    _ = (K * 2) * β * (cluster lab a).card * (cluster lab b).card := by ring
    _ = _ := by rw [hK, two_pow_mul_two h.one_le_s, h.mu_eq]

/-- The pairs of points of two clusters:
`∑_{i ∈ S_a, j ∈ S_b} q(xᵢ - xⱼ) ≤ 2^(2s-1) (n_a n_b q(m_a - m_b) + μ n_a n_b)`. -/
theorem sum_pair_x_le (a b : Fin k) :
    ∑ i ∈ cluster lab a, ∑ j ∈ cluster lab b, qf E L s (x i - x j) ≤
      2 ^ (2 * s - 1) * ((cluster lab a).card * (cluster lab b).card * qf E L s (m a - m b) +
        mu r s R e * (cluster lab a).card * (cluster lab b).card) := by
  calc ∑ i ∈ cluster lab a, ∑ j ∈ cluster lab b, qf E L s (x i - x j)
      ≤ ∑ i ∈ cluster lab a, ∑ j ∈ cluster lab b,
          2 ^ (2 * s - 1) * (qf E L s (m a - m b) + qf E L s (ζ i - ζ j)) :=
        sum_le_sum fun i hi ↦ sum_le_sum fun j hj ↦ by
          rw [h.x_sub_of_mem hi hj]
          exact h.qf_add_le _ _
    _ = 2 ^ (2 * s - 1) * ((cluster lab a).card * (cluster lab b).card * qf E L s (m a - m b) +
          ∑ i ∈ cluster lab a, ∑ j ∈ cluster lab b, qf E L s (ζ i - ζ j)) := by
        simp_rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
        ring
    _ ≤ _ := by
        gcongr
        exact h.sum_pair_zeta_le a b

/-- **Step 4**: two clusters whose centers are far apart for `q`: `q(m_a - m_b) ≥ 4^(-s)/2`. -/
theorem exists_far : ∃ a b, a ≠ b ∧ 0 < (cluster lab a).card ∧ 0 < (cluster lab b).card ∧
    (4 ^ s : ℝ)⁻¹ / 2 ≤ qf E L s (m a - m b) := by
  by_contra hcon
  push Not at hcon
  set c₀ : ℝ := (4 ^ s : ℝ)⁻¹ / 2 with hc₀
  set K : ℝ := 2 ^ (2 * s - 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hn := h.n_pos'
  have hterm : ∀ a b, ((cluster lab a).card : ℝ) * (cluster lab b).card * qf E L s (m a - m b) ≤
      ((cluster lab a).card : ℝ) * (cluster lab b).card * c₀ := fun a b ↦ by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    by_cases hab : a = b
    · rw [hab, sub_self, h.qf_zero]
      positivity
    · exact (hcon a b hab (by exact_mod_cast h.card_pos a) (by exact_mod_cast h.card_pos b)).le
  have hsum : ∑ i, ∑ j, qf E L s (x i - x j) ≤ K * (c₀ + mu r s R e) * n ^ 2 := by
    rw [sum_sum_eq_sum_cluster lab]
    calc ∑ a, ∑ b, ∑ i ∈ cluster lab a, ∑ j ∈ cluster lab b, qf E L s (x i - x j)
        ≤ ∑ a, ∑ b, K * (((cluster lab a).card : ℝ) * (cluster lab b).card * c₀ +
            mu r s R e * (cluster lab a).card * (cluster lab b).card) :=
          sum_le_sum fun a _ ↦ sum_le_sum fun b _ ↦ (h.sum_pair_x_le a b).trans
            (mul_le_mul_of_nonneg_left (add_le_add_left (hterm a b) _) hK0)
      _ = K * (c₀ + mu r s R e) * ((∑ a, ((cluster lab a).card : ℝ)) *
            ∑ b, ((cluster lab b).card : ℝ)) := by
          rw [sum_mul_sum, mul_sum]
          refine sum_congr rfl fun a _ ↦ ?_
          rw [mul_sum]
          refine sum_congr rfl fun b _ ↦ ?_
          ring
      _ = _ := by rw [sum_card_cluster, sq]
  have hlow : n ^ 2 / 2 ≤ ∑ i, ∑ j, qf E L s (x i - x j) := by
    have := h.E_pair_lower
    rw [E_pairPoly, le_inv_mul_iff₀ (by positivity)] at this
    simpa [qf, div_eq_mul_inv, mul_comm] using this
  have h1 : 1 / 2 ≤ K * (c₀ + mu r s R e) := by
    have : n ^ 2 * (1 / 2) ≤ n ^ 2 * (K * (c₀ + mu r s R e)) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hK2 : K * 2 = 4 ^ s := two_pow_mul_two h.one_le_s
  have hu : (0 : ℝ) < 4 ^ s := by positivity
  have hKc : K * c₀ = 1 / 4 := by
    rw [hc₀]
    field_simp
    linarith
  have hmu := h.mu_lt
  have : K * mu r s R e < K * c₀ := mul_lt_mul_of_pos_left hmu (by positivity)
  nlinarith

/-! #### Pair fractions -/

/-- **Same-cluster pairs** (Markov): at most `δ₁ n_c²` pairs of a cluster have
`q(xᵢ - xⱼ) > τ`, since `∑_{i, j ∈ S_c} q(xᵢ - xⱼ) = ∑_{i, j ∈ S_c} q(ζᵢ - ζⱼ) ≤ μ n_c²`. -/
theorem card_near_le (c : Fin k) :
    (((cluster lab c ×ˢ cluster lab c).filter fun ij ↦
        tauNear s < qf E L s (x ij.1 - x ij.2)).card : ℝ) ≤
      delta1 r s R e * (cluster lab c).card ^ 2 := by
  have hsum : ∑ ij ∈ cluster lab c ×ˢ cluster lab c, qf E L s (x ij.1 - x ij.2) ≤
      mu r s R e * (cluster lab c).card ^ 2 := by
    rw [sum_product]
    calc ∑ i ∈ cluster lab c, ∑ j ∈ cluster lab c, qf E L s (x i - x j)
        = ∑ i ∈ cluster lab c, ∑ j ∈ cluster lab c, qf E L s (ζ i - ζ j) :=
          sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ by rw [h.x_sub_of_mem_same hi hj]
      _ ≤ mu r s R e * (cluster lab c).card * (cluster lab c).card := h.sum_pair_zeta_le c c
      _ = _ := by ring
  refine (card_filter_lt_le _ _ (fun _ _ ↦ h.qf_nonneg _) (tauNear_pos s)).trans ?_
  rw [div_le_iff₀ (tauNear_pos s)]
  refine hsum.trans (le_of_eq ?_)
  rw [delta1_eq, tauNear]
  field_simp

/-- **Far pairs** (Markov): if `q(m_a - m_b) ≥ 4^(-s)/2`, at most `δ₁ n_a n_b` pairs of
`S_a × S_b` have `q(xᵢ - xⱼ) < T`. For them `q(ζᵢ - ζⱼ) > T`, by the weak triangle inequality
`q(m_a - m_b) ≤ 2^(2s-1) (q(xᵢ - xⱼ) + q(ζᵢ - ζⱼ))`. -/
theorem card_far_le {a b : Fin k} (hab : (4 ^ s : ℝ)⁻¹ / 2 ≤ qf E L s (m a - m b)) :
    (((cluster lab a ×ˢ cluster lab b).filter fun ij ↦
        qf E L s (x ij.1 - x ij.2) < thrFar s).card : ℝ) ≤
      delta1 r s R e * (cluster lab a).card * (cluster lab b).card := by
  have hu : (0 : ℝ) < 4 ^ s := by positivity
  have hK2 : (2 : ℝ) ^ (2 * s - 1) * 2 = 4 ^ s := two_pow_mul_two h.one_le_s
  have hT : thrFar s = 1 / (2 * ((4 : ℝ) ^ s) ^ 2) := by rw [thrFar, sixteen_pow]
  have hsub : ((cluster lab a ×ˢ cluster lab b).filter fun ij ↦
      qf E L s (x ij.1 - x ij.2) < thrFar s) ⊆
      (cluster lab a ×ˢ cluster lab b).filter fun ij ↦ thrFar s < qf E L s (ζ ij.1 - ζ ij.2) := by
    intro ij hij
    rw [mem_filter, mem_product] at hij ⊢
    obtain ⟨⟨hi, hj⟩, hlt⟩ := hij
    refine ⟨⟨hi, hj⟩, ?_⟩
    have htri : qf E L s (m a - m b) ≤
        2 ^ (2 * s - 1) * (qf E L s (x ij.1 - x ij.2) + qf E L s (ζ ij.1 - ζ ij.2)) := by
      have hx : m a - m b = (x ij.1 - x ij.2) + -(ζ ij.1 - ζ ij.2) := by
        rw [h.x_sub_of_mem hi hj]
        abel
      rw [hx, ← h.qf_neg (ζ ij.1 - ζ ij.2)]
      exact h.qf_add_le _ _
    set u : ℝ := 4 ^ s
    set Q := qf E L s (x ij.1 - x ij.2)
    set Q' := qf E L s (ζ ij.1 - ζ ij.2)
    rw [hT] at hlt ⊢
    rw [lt_div_iff₀ (by positivity)] at hlt
    rw [div_lt_iff₀ (by positivity)]
    -- `u⁻¹/2 ≤ (u/2) (Q + Q')`, so `1 ≤ u² (Q + Q')`.
    have h1 : u⁻¹ / 2 ≤ u / 2 * (Q + Q') := by
      have : (2 : ℝ) ^ (2 * s - 1) = u / 2 := by rw [← hK2]; ring
      rw [← this]
      exact hab.trans htri
    have h2 : 1 ≤ u ^ 2 * (Q + Q') := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * u)
      rw [show 2 * u * (u⁻¹ / 2) = 1 by field_simp] at this
      nlinarith
    nlinarith
  have hsum : ∑ ij ∈ cluster lab a ×ˢ cluster lab b, qf E L s (ζ ij.1 - ζ ij.2) ≤
      mu r s R e * (cluster lab a).card * (cluster lab b).card := by
    rw [sum_product]
    exact h.sum_pair_zeta_le a b
  have hmu := h.mu_nonneg
  have hpos : 0 ≤ mu r s R e * (cluster lab a).card * (cluster lab b).card := by positivity
  have hu1 : (1 : ℝ) ≤ 4 ^ s := one_le_pow₀ (by norm_num)
  calc (((cluster lab a ×ˢ cluster lab b).filter fun ij ↦
        qf E L s (x ij.1 - x ij.2) < thrFar s).card : ℝ)
      ≤ ((cluster lab a ×ˢ cluster lab b).filter fun ij ↦
          thrFar s < qf E L s (ζ ij.1 - ζ ij.2)).card := by exact_mod_cast card_le_card hsub
    _ ≤ (∑ ij ∈ cluster lab a ×ˢ cluster lab b, qf E L s (ζ ij.1 - ζ ij.2)) / thrFar s :=
        card_filter_lt_le _ _ (fun _ _ ↦ h.qf_nonneg _) (thrFar_pos s)
    _ ≤ mu r s R e * (cluster lab a).card * (cluster lab b).card / thrFar s :=
        div_le_div_of_nonneg_right hsum (thrFar_pos s).le
    _ = mu r s R e * (cluster lab a).card * (cluster lab b).card * (2 * ((4 : ℝ) ^ s) ^ 2) := by
        rw [hT]
        field_simp
    _ ≤ mu r s R e * (cluster lab a).card * (cluster lab b).card * (4 * ((4 : ℝ) ^ s) ^ 3) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hpos
    _ = _ := by
        rw [delta1_eq, sixtyfour_pow]
        ring

/-! #### The hypotheses of the rounding step -/

theorem qf_x_nonneg (i j : Fin n) : 0 ≤ qf E L s (x i - x j) := h.qf_nonneg _

theorem qf_x_symm (i j : Fin n) : qf E L s (x i - x j) = qf E L s (x j - x i) :=
  h.qf_sub_comm _ _

/-- The weak triangle inequality `Q i j ≤ 2^(2s-1) (Q i p + Q p j)` for `Q i j = q(xᵢ - xⱼ)`. -/
theorem qf_x_tri (i j p : Fin n) :
    qf E L s (x i - x j) ≤ 2 ^ (2 * s - 1) * (qf E L s (x i - x p) + qf E L s (x p - x j)) := by
  rw [← sub_add_sub_cancel (x i) (x p) (x j)]
  exact h.qf_add_le _ _

theorem two_mul_K_mul_tau_lt : 2 * 2 ^ (2 * s - 1) * tauNear s < thrFar s :=
  two_mul_two_pow_mul_tauNear_lt h.one_le_s

theorem delta1_le : delta1 r s R e ≤ 1 / 10000 := h.small_delta

/-- **Everything the rounding step needs**, for `Q i j = q(xᵢ - xⱼ)`, `K = 2^(2s-1)`, the
thresholds `τ = 1/(4·64^s)`, `T = 16^(-s)/2` and `δ₁ = 4·64^s μ ≤ 10⁻⁴`: `Q ≥ 0`, `Q` is
symmetric, `Q i j ≤ K (Q i p + Q p j)`, `2 K τ < T`, at most `δ₁ n_c²` pairs of each cluster have
`Q > τ`, and for two distinct nonempty clusters `S_a`, `S_b` at most `δ₁ n_a n_b` pairs of
`S_a × S_b` have `Q < T`. -/
theorem rounding_hyps :
    (∀ i j, 0 ≤ qf E L s (x i - x j)) ∧
    (∀ i j, qf E L s (x i - x j) = qf E L s (x j - x i)) ∧
    (∀ i j p, qf E L s (x i - x j) ≤
      2 ^ (2 * s - 1) * (qf E L s (x i - x p) + qf E L s (x p - x j))) ∧
    2 * 2 ^ (2 * s - 1) * tauNear s < thrFar s ∧
    delta1 r s R e ≤ 1 / 10000 ∧
    (∀ c, (((cluster lab c ×ˢ cluster lab c).filter fun ij ↦
        tauNear s < qf E L s (x ij.1 - x ij.2)).card : ℝ) ≤
      delta1 r s R e * (cluster lab c).card ^ 2) ∧
    ∃ a b, a ≠ b ∧ (cluster lab a).Nonempty ∧ (cluster lab b).Nonempty ∧
      (((cluster lab a ×ˢ cluster lab b).filter fun ij ↦
          qf E L s (x ij.1 - x ij.2) < thrFar s).card : ℝ) ≤
        delta1 r s R e * (cluster lab a).card * (cluster lab b).card := by
  obtain ⟨a, b, hab, ha, hb, hq⟩ := h.exists_far
  exact ⟨h.qf_x_nonneg, h.qf_x_symm, h.qf_x_tri, h.two_mul_K_mul_tau_lt, h.delta1_le,
    h.card_near_le, a, b, hab, Finset.card_pos.1 ha, Finset.card_pos.1 hb, h.card_far_le hq⟩

end PAHyp

end BS23.Separating
