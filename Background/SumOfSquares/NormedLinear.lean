module

public import Background.SumOfSquares.Normed
public import Background.SumOfSquares.PowerSOS

/-!
# Normed proofs using boundedly many constraints

`SoS.DerivesNq A k M q g` is exactly `DerivesN` with all multipliers on sets of more than
`q` constraints zero. In particular, `q = 1` means linear dependence on the constraints.

* `SoS.DerivesNq.derivesN` gives the existing approximate soundness theorem.
* `SoS.DerivesNq.of_mem`, `ofIsSOS`, `add`, `mulSOS`, `smul`, `mono`, `congr` are the normed rules.
* `SoS.DerivesNq.trans` composes linear proofs without increasing their degree.
* `SoS.DerivesNq.ball_pow` and `dehomogenize` remove powers of the squared norm.
* `SoS.DerivesNq.sqrt_sub`, `sqrt_add`, and `root` take roots of constant upper bounds.

The root rules use additive norm bounds in place of the maxima in the design notes; their
statements give the explicit constants. The systems remain lists, so composition counts list
entries, including repeated constraints.
-/

@[expose] public section

namespace SoS

open MvPolynomial Finset

variable {σ : Type*}

/-- A normed proof whose nonzero multipliers use at most `q` constraints. -/
def DerivesNq (A : System σ ℝ) (k : ℕ) (M : ℝ) (q : ℕ) (g : MvPolynomial σ ℝ) : Prop :=
  ∃ P : Proof A g k, (∀ S, coeffNorm1 (P.mult S) ≤ M) ∧
    ∀ S, q < S.card → P.mult S = 0

namespace DerivesNq

variable {A B : System σ ℝ} {k k' q q' : ℕ} {M M' M₁ M₂ : ℝ}
  {g g' g₁ g₂ : MvPolynomial σ ℝ}

theorem derivesN (h : DerivesNq A k M q g) : DerivesN A k M g :=
  ⟨h.choose, h.choose_spec.1⟩

theorem nonneg (h : DerivesNq A k M q g) : 0 ≤ M := h.derivesN.nonneg

theorem mono (h : DerivesNq A k M q g) (hk : k ≤ k') (hM : M ≤ M') :
    DerivesNq A k' M' q g := by
  obtain ⟨P, hn, hq⟩ := h
  exact ⟨P.weaken hk, (fun S ↦ (hn S).trans hM), hq⟩

theorem mono_q (h : DerivesNq A k M q g) (hq : q ≤ q') : DerivesNq A k M q' g := by
  obtain ⟨P, hn, hP⟩ := h
  exact ⟨P, hn, fun S hS ↦ hP S (lt_of_le_of_lt hq hS)⟩

theorem congr (h : DerivesNq A k M q g) (e : g = g') : DerivesNq A k M q g' := e ▸ h

theorem zero (A : System σ ℝ) (k q : ℕ) (hM : 0 ≤ M) : DerivesNq A k M q 0 :=
  ⟨Proof.zero A k, (fun _ ↦ by simpa [Proof.zero] using hM), fun _ _ ↦ rfl⟩

theorem ofIsSOS (A : System σ ℝ) {p : MvPolynomial σ ℝ} (hp : IsSOS p)
    (hdeg : p.totalDegree ≤ k) (hM : coeffNorm1 p ≤ M) : DerivesNq A k M q p := by
  refine ⟨Proof.ofIsSOS A hp hdeg, ?_, ?_⟩
  · intro S
    simp only [Proof.ofIsSOS]
    split_ifs
    · exact hM
    · simpa using (coeffNorm1_nonneg p).trans hM
  · intro S hS
    have : S ≠ ∅ := by intro h; simp [h] at hS
    simp [Proof.ofIsSOS, this]

theorem of_mem {f : MvPolynomial σ ℝ} (hf : f ∈ A) (hdeg : f.totalDegree ≤ k)
    (hM : 1 ≤ M) (hq : 1 ≤ q := by omega) : DerivesNq A k M q f := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hf
  refine ⟨Proof.assumption A i hdeg, ?_, ?_⟩
  · intro S
    simp only [Proof.assumption]
    split_ifs
    · simpa [coeffNorm1_one] using hM
    · simpa using zero_le_one.trans hM
  · intro S hS
    have : S ≠ {i} := by intro h; simp [h] at hS; omega
    simp [Proof.assumption, this]

theorem add (h₁ : DerivesNq A k M₁ q g₁) (h₂ : DerivesNq A k M₂ q g₂) :
    DerivesNq A k (M₁ + M₂) q (g₁ + g₂) := by
  obtain ⟨P₁, hn₁, hq₁⟩ := h₁
  obtain ⟨P₂, hn₂, hq₂⟩ := h₂
  refine ⟨P₁.add P₂, fun S ↦ (coeffNorm1_add_le _ _).trans
    (add_le_add (hn₁ S) (hn₂ S)), ?_⟩
  intro S hS
  simp [Proof.add, hq₁ S hS, hq₂ S hS]

theorem mulSOS {s : MvPolynomial σ ℝ} (hs : IsSOS s) (h : DerivesNq A k M q g) :
    DerivesNq A (s.totalDegree + k) (coeffNorm1 s * M) q (s * g) := by
  obtain ⟨P, hn, hq⟩ := h
  refine ⟨P.mulSOS hs, fun S ↦ (coeffNorm1_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (hn S) (coeffNorm1_nonneg _)), ?_⟩
  intro S hS
  simp [Proof.mulSOS, hq S hS]

theorem smul {c : ℝ} (hc : 0 ≤ c) (h : DerivesNq A k M q g) :
    DerivesNq A k (c * M) q (C c * g) := by
  have := h.mulSOS (IsSOS.const hc)
  rwa [totalDegree_C, zero_add, coeffNorm1_C, abs_of_nonneg hc] at this

theorem sum {ι : Type*} (s : Finset ι) {g : ι → MvPolynomial σ ℝ} {M : ι → ℝ}
    (h : ∀ i ∈ s, DerivesNq A k (M i) q (g i)) :
    DerivesNq A k (∑ i ∈ s, M i) q (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero A k q le_rfl
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi ↦ h i (mem_insert_of_mem hi))

end DerivesNq

/-- A proof supported on empty sets and singletons is linear in the listed constraints. -/
theorem Proof.eq_sum_linear {A : System σ ℝ} {g : MvPolynomial σ ℝ} {k : ℕ}
    (P : Proof A g k) (hq : ∀ S, 1 < S.card → P.mult S = 0) :
    g = P.mult ∅ + ∑ i, P.mult {i} * A.get i := by
  classical
  let T : Finset (Finset (Fin A.length)) := insert ∅ (univ.image fun i ↦ {i})
  have he : (∅ : Finset (Fin A.length)) ∉ univ.image (fun i ↦ {i}) := by simp
  conv_lhs => rw [P.eq_sum]
  rw [← sum_subset (subset_univ T)]
  · simp only [T, sum_insert he, System.prod_empty, mul_one]
    rw [sum_image]
    · simp [System.prod]
    · intro i _ j _ h
      simpa using h
  · intro S _ hS
    have hc : 1 < S.card := by
      by_contra hc
      have : S.card = 0 ∨ S.card = 1 := by omega
      rcases this with h | h
      · exact hS (by simp [T, card_eq_zero.1 h])
      · obtain ⟨i, rfl⟩ := card_eq_one.1 h
        exact hS (by simp [T])
    rw [hq S hc, zero_mul]

namespace DerivesNq

variable {A B : System σ ℝ} {k : ℕ} {M M' : ℝ} {g : MvPolynomial σ ℝ}

/-- Linear composition preserves the degree and pays once for each entry of `B`. -/
theorem trans (hAB : ∀ f ∈ B, DerivesNq A f.totalDegree M 1 f)
    (h : DerivesNq B k M' 1 g) :
    DerivesNq A k (M' * (1 + B.length * M)) 1 g := by
  classical
  obtain ⟨P, hn, hq⟩ := h
  have hM' : 0 ≤ M' := (coeffNorm1_nonneg _).trans (hn ∅)
  have h₀ : DerivesNq A k M' 1 (P.mult ∅) := ofIsSOS A (P.isSOS_mult ∅) (by
    by_cases h₀ : P.mult ∅ = 0
    · simp [h₀]
    · simpa using P.degree_le ∅ h₀) (hn ∅)
  have hi : ∀ i : Fin B.length,
      DerivesNq A k (M' * M) 1 (P.mult {i} * B.get i) := by
    intro i
    have hf := hAB _ (List.get_mem B i)
    by_cases hz : P.mult {i} = 0
    · simpa [hz] using zero A k 1 (mul_nonneg hM' hf.nonneg)
    · have hd := P.degree_le {i} hz
      refine (hf.mulSOS (P.isSOS_mult {i})).mono ?_ ?_
      · simpa [System.degree] using hd
      · exact mul_le_mul_of_nonneg_right (hn {i}) hf.nonneg
  have hs := h₀.add (sum univ fun i _ ↦ hi i)
  rw [← P.eq_sum_linear hq] at hs
  convert hs using 1
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end DerivesNq

private theorem geom_sum_le_add_one_pow {b : ℝ} (hb : 0 ≤ b) (m : ℕ) :
    ∑ i ∈ range m, b ^ i ≤ (b + 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [geom_sum_succ, pow_succ]
    have := one_le_pow₀ (show 1 ≤ b + 1 by linarith) (n := m)
    nlinarith

namespace DerivesNq

variable {A : System σ ℝ} {k q : ℕ} {M : ℝ} {g : MvPolynomial σ ℝ}

/-- Powers of any sum of squares bounded by one, with a coefficient norm bound `b`. -/
theorem one_sub_pow {p : MvPolynomial σ ℝ} (hp : IsSOS p) (hf : 1 - p ∈ A)
    {e : ℕ} (hd : p.totalDegree ≤ e) {b : ℝ} (hn : coeffNorm1 p ≤ b) (m : ℕ) :
    DerivesNq A (e * m) ((b + 1) ^ m) 1 (1 - p ^ m) := by
  classical
  have hb : 0 ≤ b := (coeffNorm1_nonneg _).trans hn
  cases m with
  | zero => simpa using zero A 0 1 (by norm_num : (0 : ℝ) ≤ 1)
  | succ m =>
    let s := ∑ i ∈ range (m + 1), p ^ i
    have hs : IsSOS s := by
      apply IsSOS.sum
      intro i _
      simpa [IsSOS, toReal_real] using isSumSq_pow (by simpa [IsSOS] using hp) i
    have hsd : s.totalDegree ≤ m * e := totalDegree_finsetSum_le fun i hi ↦
      (totalDegree_pow _ _).trans (by
        have := mem_range.1 hi
        exact (Nat.mul_le_mul_left i hd).trans (Nat.mul_le_mul_right e (by omega)))
    have hsn : coeffNorm1 s ≤ (b + 1) ^ (m + 1) := by
      refine (coeffNorm1_sum_le _ _).trans (le_trans (sum_le_sum fun i _ ↦ ?_)
        (geom_sum_le_add_one_pow hb (m + 1)))
      exact (coeffNorm1_pow_le _ _).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) hn i)
    have hd₁ : (1 - p).totalDegree ≤ e :=
      (totalDegree_sub _ _).trans (max_le (by simp) hd)
    have h := (of_mem (q := 1) hf hd₁ le_rfl).mulSOS hs
    refine (h.mono (k' := e * (m + 1)) (by nlinarith) ?_).congr
      (geom_sum_mul_neg p (m + 1))
    simpa using hsn

/-- K3: powers of the unit ball constraint in any finite variable type. -/
theorem ball_pow [Fintype σ]
    (hf : 1 - ∑ i : σ, (X i : MvPolynomial σ ℝ) ^ 2 ∈ A) (m : ℕ) :
    DerivesNq A (2 * m) (((Fintype.card σ : ℝ) + 1) ^ m) 1
      (1 - (∑ i : σ, (X i : MvPolynomial σ ℝ) ^ 2) ^ m) := by
  classical
  refine one_sub_pow (IsSOS.sum _ fun i _ ↦ IsSOS.sq (X i)) hf
    (totalDegree_finsetSum_le fun i _ ↦ by rw [totalDegree_X_pow]) ?_ m
  refine (coeffNorm1_sum_le _ _).trans ?_
  calc ∑ i : σ, coeffNorm1 ((X i : MvPolynomial σ ℝ) ^ 2)
      ≤ ∑ _i : σ, (1 : ℝ) := sum_le_sum fun i _ ↦ by
        simpa [coeffNorm1_X] using coeffNorm1_pow_le (X i : MvPolynomial σ ℝ) 2
    _ = Fintype.card σ := by simp

/-- K3: replace `e N^m - g` by `e - g` using the unit ball constraint. -/
theorem dehomogenize [Fintype σ]
    (hf : 1 - ∑ i : σ, (X i : MvPolynomial σ ℝ) ^ 2 ∈ A)
    {e : ℝ} (he : 0 ≤ e) {m : ℕ}
    (h : DerivesNq A k M 1
      (C e * (∑ i : σ, (X i : MvPolynomial σ ℝ) ^ 2) ^ m - g)) :
    DerivesNq A (max k (2 * m)) (M + e * ((Fintype.card σ : ℝ) + 1) ^ m) 1 (C e - g) := by
  have h₁ := h.mono (le_max_left k (2 * m)) le_rfl
  have h₂ := ((ball_pow hf m).smul he).mono (le_max_right k _) le_rfl
  exact (h₁.add h₂).congr (by ring)

/-- K8: a constant square bound implies an upper bound, with an additive norm bound. -/
theorem sqrt_sub {e : ℝ} (he : 0 < e) {x : MvPolynomial σ ℝ}
    (h : DerivesNq A k M q (C (e ^ 2) - x ^ 2)) :
    DerivesNq A (max k (2 * x.totalDegree))
      ((M + (coeffNorm1 x + e) ^ 2) / (2 * e)) q (C e - x) := by
  have hd : ((C e - x) ^ 2).totalDegree ≤ 2 * x.totalDegree :=
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2
      ((totalDegree_sub _ _).trans (max_le (by simp) le_rfl)))
  have hn : coeffNorm1 ((C e - x) ^ 2) ≤ (coeffNorm1 x + e) ^ 2 := by
    refine (coeffNorm1_pow_le _ _).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) ?_ 2)
    have := coeffNorm1_sub_le (C e : MvPolynomial σ ℝ) x
    rw [coeffNorm1_C, abs_of_pos he] at this
    linarith
  have hs := ofIsSOS (q := q) A (IsSOS.sq (C e - x)) (hd.trans (le_max_right k _)) hn
  have ht := ((h.mono (le_max_left _ _) le_rfl).add hs).smul
    (show 0 ≤ 1 / (2 * e) by positivity)
  have hc : (C (1 / (2 * e)) * C (2 * e) : MvPolynomial σ ℝ) = 1 := by
    rw [← C_mul, one_div_mul_cancel (ne_of_gt (by positivity : 0 < 2 * e)), C_1]
  have hx : C (e ^ 2) - x ^ 2 + (C e - x) ^ 2 = C (2 * e) * (C e - x) := by
    simp only [C_pow, C_mul, map_ofNat]
    ring
  convert ht.congr (by rw [hx, ← mul_assoc, hc, one_mul]) using 1
  ring

/-- K8: the corresponding lower bound. -/
theorem sqrt_add {e : ℝ} (he : 0 < e) {x : MvPolynomial σ ℝ}
    (h : DerivesNq A k M q (C (e ^ 2) - x ^ 2)) :
    DerivesNq A (max k (2 * x.totalDegree))
      ((M + (coeffNorm1 x + e) ^ 2) / (2 * e)) q (C e + x) := by
  have ht := sqrt_sub (x := -x) he (h.congr (by ring))
  simpa [totalDegree_neg, coeffNorm1_neg] using ht

end DerivesNq

private theorem isSOS_root_gap {Q : MvPolynomial σ ℝ} (hQ : IsSOS Q)
    {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    IsSOS (Q ^ (m + 1) - C (((m : ℝ) + 1) * c ^ m) * Q + C (m * c ^ (m + 1))) := by
  induction m with
  | zero => simpa using (IsSOS.zero (σ := σ) (K := ℝ))
  | succ m ih =>
    have hs := (IsSOS.const (show 0 ≤ ((m : ℝ) + 1) * c ^ m by positivity)).mul
      (IsSOS.sq (Q - C c))
    convert (hQ.mul ih).add hs using 1
    push_cast
    simp only [pow_succ, C_mul, C_add, C_pow, C_1]
    ring

namespace DerivesNq

/-- K9: take the root of a constant upper bound for a sum of squares.
The norm bound uses the triangle inequality on the homogeneous tangent polynomial. -/
theorem root {A : System σ ℝ} {k q r : ℕ} {M c : ℝ} {Q : MvPolynomial σ ℝ}
    (hQ : IsSOS Q) (hc : 0 < c) (hr : 1 ≤ r)
    (h : DerivesNq A k M q (C (c ^ r) - Q ^ r)) :
    DerivesNq A (max k (r * Q.totalDegree))
      ((M + coeffNorm1 Q ^ r + (r : ℝ) * c ^ (r - 1) * coeffNorm1 Q +
        ((r : ℝ) - 1) * c ^ r) / ((r : ℝ) * c ^ (r - 1))) q (C c - Q) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  let a : ℝ := ((m : ℝ) + 1) * c ^ m
  let T := Q ^ (m + 1) - C a * Q + C ((m : ℝ) * c ^ (m + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have hTd : T.totalDegree ≤ (m + 1) * Q.totalDegree := by
    refine (totalDegree_add _ _).trans (max_le ?_ (by rw [totalDegree_C]; omega))
    refine (totalDegree_sub _ _).trans (max_le (totalDegree_pow _ _) ?_)
    have hd := totalDegree_mul (C a : MvPolynomial σ ℝ) Q
    rw [totalDegree_C, zero_add] at hd
    exact hd.trans (by nlinarith)
  have hTn : coeffNorm1 T ≤ coeffNorm1 Q ^ (m + 1) + a * coeffNorm1 Q +
      (m : ℝ) * c ^ (m + 1) := by
    refine (coeffNorm1_add_le _ _).trans ?_
    refine add_le_add ((coeffNorm1_sub_le _ _).trans (add_le_add
      (coeffNorm1_pow_le _ _) ?_)) ?_
    · rw [coeffNorm1_C_mul, abs_of_pos ha]
    · rw [coeffNorm1_C, abs_of_nonneg (by positivity)]
  have hTs : IsSOS T := isSOS_root_gap hQ hc.le m
  have hs := ofIsSOS (q := q) A hTs (hTd.trans (le_max_right k _)) hTn
  have ht := ((h.mono (le_max_left _ _) le_rfl).add hs).smul (inv_nonneg.2 ha.le)
  have he : C (c ^ (m + 1)) - Q ^ (m + 1) + T = C a * (C c - Q) := by
    dsimp [T, a]
    simp only [pow_succ, C_mul, C_add, C_pow, C_1]
    ring
  have hi : (C a⁻¹ * C a : MvPolynomial σ ℝ) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ ha.ne', C_1]
  have ht' := ht.congr (by rw [he, ← mul_assoc, hi, one_mul])
  convert ht' using 1
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  dsimp [a]
  ring

end DerivesNq

end SoS
