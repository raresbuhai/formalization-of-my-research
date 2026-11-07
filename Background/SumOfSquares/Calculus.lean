module

public import Background.SumOfSquares.Proof
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The calculus of sum-of-squares proofs

Rules for building sum-of-squares proofs from others.

* `SoS.Proof.weaken`: a proof of degree `k` is one of every degree `k' ≥ k`.
* `SoS.Proof.zero`, `SoS.Proof.one`, `SoS.Proof.ofIsSOS`: proofs of `0 ≥ 0`, of `1 ≥ 0`, and of
  `p ≥ 0` for a sum of squares `p`.
* `SoS.Proof.assumption`: a constraint of `A` follows from `A`.
* `SoS.Proof.add`, `SoS.Derives.sum`: sums of proofs.
* `SoS.Proof.mulSOS`: multiplying a proof by a sum of squares (for example a nonnegative
  constant).
* `SoS.Derives.mul_eq`: if `A` contains both `h ≥ 0` and `-h ≥ 0`, it proves `q h ≥ 0` for every
  polynomial `q`.
* `SoS.Proof.subst`, `SoS.Derives.subst`: substituting polynomials of degree at most `e` for the
  variables multiplies the degree by `e`. Facts stated for indeterminates are used this way.
* `SoS.Derives.trans`: composition. If `A` proves every constraint of `B` in degree `k`, and `B`
  (with nonconstant constraints) proves `g ≥ 0` in degree `k'`, then `A` proves `g ≥ 0` in degree
  `k' max k 1`.
* `SoS.Proof.mul`: from proofs of `g₁ ≥ 0` and `g₂ ≥ 0` of degrees `k₁` and `k₂`, a proof of
  `g₁ g₂ ≥ 0` of degree `k₁ + k₂`. A constraint used by both proofs appears squared in the
  product; the square moves into the sum-of-squares multiplier.
* `SoS.Derives.prod`: products of finitely many derived polynomials.
-/

@[expose] public section

namespace SoS

open MvPolynomial

variable {σ K : Type*} [Field K]

section toReal

variable [Algebra K ℝ]

@[simp] theorem toReal_zero : toReal (0 : MvPolynomial σ K) = 0 := map_zero _

@[simp] theorem toReal_one : toReal (1 : MvPolynomial σ K) = 1 := map_one _

@[simp] theorem toReal_add (p q : MvPolynomial σ K) : toReal (p + q) = toReal p + toReal q :=
  map_add _ _ _

@[simp] theorem toReal_mul (p q : MvPolynomial σ K) : toReal (p * q) = toReal p * toReal q :=
  map_mul _ _ _

@[simp] theorem toReal_pow (p : MvPolynomial σ K) (n : ℕ) : toReal (p ^ n) = toReal p ^ n :=
  map_pow _ _ _

@[simp] theorem toReal_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ K) :
    toReal (∑ i ∈ s, f i) = ∑ i ∈ s, toReal (f i) := by
  unfold toReal
  exact map_sum _ _ _

@[simp] theorem toReal_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ K) :
    toReal (∏ i ∈ s, f i) = ∏ i ∈ s, toReal (f i) := by
  unfold toReal
  exact map_prod _ _ _

theorem totalDegree_toReal_le (p : MvPolynomial σ K) :
    (toReal p).totalDegree ≤ p.totalDegree := by
  unfold toReal totalDegree
  exact Finset.sup_mono (support_map_subset _ _)

end toReal

namespace IsSOS

variable [Algebra K ℝ]

theorem zero : IsSOS (0 : MvPolynomial σ K) := by
  simp [IsSOS]

theorem one : IsSOS (1 : MvPolynomial σ K) := by
  simp [IsSOS]

theorem add {p q : MvPolynomial σ K} (hp : IsSOS p) (hq : IsSOS q) : IsSOS (p + q) := by
  simpa [IsSOS] using IsSumSq.add hp hq

theorem mul {p q : MvPolynomial σ K} (hp : IsSOS p) (hq : IsSOS q) : IsSOS (p * q) := by
  simpa [IsSOS] using IsSumSq.mul hp hq

theorem sq (p : MvPolynomial σ K) : IsSOS (p ^ 2) := by
  simp [IsSOS, pow_two]

theorem sum {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial σ K} (h : ∀ i ∈ s, IsSOS (f i)) :
    IsSOS (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

end IsSOS

namespace System

variable (A : System σ K)

@[simp] theorem prod_empty : A.prod ∅ = 1 := Finset.prod_empty

@[simp] theorem degree_empty : A.degree ∅ = 0 := Finset.sum_empty

theorem totalDegree_prod_le (S : Finset (Fin A.length)) : (A.prod S).totalDegree ≤ A.degree S :=
  totalDegree_finsetProd _ _

/-- Multiplying the constraints in `S₁` by those in `S₂` gives the square of those in both,
times those in exactly one. -/
theorem prod_mul_prod (S₁ S₂ : Finset (Fin A.length)) :
    A.prod S₁ * A.prod S₂ = A.prod (S₁ ∩ S₂) ^ 2 * A.prod (symmDiff S₁ S₂) := by
  classical
  have h₁ : A.prod S₁ = A.prod (S₁ \ S₂) * A.prod (S₁ ∩ S₂) := by
    unfold System.prod
    rw [← Finset.prod_union (Finset.disjoint_sdiff_inter S₁ S₂), Finset.sdiff_union_inter]
  have h₂ : A.prod S₂ = A.prod (S₂ \ S₁) * A.prod (S₁ ∩ S₂) := by
    unfold System.prod
    rw [Finset.inter_comm, ← Finset.prod_union (Finset.disjoint_sdiff_inter S₂ S₁),
      Finset.sdiff_union_inter]
  have h₃ : A.prod (symmDiff S₁ S₂) = A.prod (S₁ \ S₂) * A.prod (S₂ \ S₁) := by
    unfold System.prod
    rw [Finset.symmDiff_def, Finset.prod_union disjoint_sdiff_sdiff]
  rw [h₁, h₂, h₃]
  ring

/-- The degree count of `prod_mul_prod`. -/
theorem degree_add_degree (S₁ S₂ : Finset (Fin A.length)) :
    A.degree S₁ + A.degree S₂ = 2 * A.degree (S₁ ∩ S₂) + A.degree (symmDiff S₁ S₂) := by
  classical
  have h₁ : A.degree S₁ = A.degree (S₁ \ S₂) + A.degree (S₁ ∩ S₂) := by
    unfold System.degree
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S₁ S₂), Finset.sdiff_union_inter]
  have h₂ : A.degree S₂ = A.degree (S₂ \ S₁) + A.degree (S₁ ∩ S₂) := by
    unfold System.degree
    rw [Finset.inter_comm, ← Finset.sum_union (Finset.disjoint_sdiff_inter S₂ S₁),
      Finset.sdiff_union_inter]
  have h₃ : A.degree (symmDiff S₁ S₂) = A.degree (S₁ \ S₂) + A.degree (S₂ \ S₁) := by
    unfold System.degree
    rw [Finset.symmDiff_def, Finset.sum_union disjoint_sdiff_sdiff]
  omega

end System

namespace Proof

variable [Algebra K ℝ] {A : System σ K}

/-- A proof of degree `k` is a proof of every degree `k' ≥ k`. -/
def weaken {g : MvPolynomial σ K} {k k' : ℕ} (P : Proof A g k) (h : k ≤ k') : Proof A g k' where
  mult := P.mult
  isSOS_mult := P.isSOS_mult
  degree_le S hS := (P.degree_le S hS).trans h
  eq_sum := P.eq_sum

/-- The proof of `0 ≥ 0`, in every degree. -/
noncomputable def zero (A : System σ K) (k : ℕ) : Proof A 0 k where
  mult _ := 0
  isSOS_mult _ := IsSOS.zero
  degree_le _ h := absurd rfl h
  eq_sum := by simp

/-- A sum of squares `p` of degree at most `k` has a degree-`k` proof that `p ≥ 0`. -/
noncomputable def ofIsSOS (A : System σ K) {p : MvPolynomial σ K} (hp : IsSOS p) {k : ℕ}
    (hdeg : p.totalDegree ≤ k) : Proof A p k where
  mult S := if S = ∅ then p else 0
  isSOS_mult S := by
    split_ifs
    exacts [hp, IsSOS.zero]
  degree_le S hS := by
    split_ifs at hS ⊢ with h
    · subst h
      simpa using hdeg
    · exact absurd rfl hS
  eq_sum := by
    classical
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro S _ hS
      simp [hS]
    · simp

/-- A constraint `fᵢ` of `A` of degree at most `k` has a degree-`k` proof from `A`. -/
noncomputable def assumption (A : System σ K) (i : Fin A.length) {k : ℕ}
    (hdeg : (A.get i).totalDegree ≤ k) : Proof A (A.get i) k where
  mult S := if S = {i} then 1 else 0
  isSOS_mult S := by
    split_ifs
    exacts [IsSOS.one, IsSOS.zero]
  degree_le S hS := by
    split_ifs at hS ⊢ with h
    · subst h
      simpa [System.degree] using hdeg
    · exact absurd rfl hS
  eq_sum := by
    classical
    rw [Finset.sum_eq_single {i}]
    · simp [System.prod]
    · intro S _ hS
      simp [hS]
    · simp

/-- **Sum of proofs** of the same degree. -/
noncomputable def add {g₁ g₂ : MvPolynomial σ K} {k : ℕ} (P₁ : Proof A g₁ k) (P₂ : Proof A g₂ k) :
    Proof A (g₁ + g₂) k where
  mult S := P₁.mult S + P₂.mult S
  isSOS_mult S := (P₁.isSOS_mult S).add (P₂.isSOS_mult S)
  degree_le S hS := by
    have hadd := totalDegree_add (P₁.mult S) (P₂.mult S)
    by_cases h₁ : P₁.mult S = 0
    · rw [h₁, zero_add] at hS ⊢
      exact P₂.degree_le S hS
    by_cases h₂ : P₂.mult S = 0
    · rw [h₂, add_zero] at hS ⊢
      exact P₁.degree_le S h₁
    have d₁ := P₁.degree_le S h₁
    have d₂ := P₂.degree_le S h₂
    have := max_le_iff.2 ⟨d₁, d₂⟩
    omega
  eq_sum := by
    conv_lhs => rw [P₁.eq_sum, P₂.eq_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun S _ ↦ (add_mul _ _ _).symm

/-- **Multiplying a proof by a sum of squares** `q`: from a degree-`k` proof of `g ≥ 0`, a proof of
`q g ≥ 0` of degree `deg q + k`. -/
noncomputable def mulSOS {q : MvPolynomial σ K} (hq : IsSOS q) {g : MvPolynomial σ K} {k : ℕ}
    (P : Proof A g k) : Proof A (q * g) (q.totalDegree + k) where
  mult S := q * P.mult S
  isSOS_mult S := hq.mul (P.isSOS_mult S)
  degree_le S hS := by
    have hm : P.mult S ≠ 0 := fun h ↦ hS (by rw [h, mul_zero])
    have := P.degree_le S hm
    have := totalDegree_mul q (P.mult S)
    omega
  eq_sum := by
    conv_lhs => rw [P.eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun S _ ↦ (mul_assoc _ _ _).symm

/-- The degree-`0` proof of `1 ≥ 0`. -/
noncomputable def one (A : System σ K) : Proof A 1 0 where
  mult S := if S = ∅ then 1 else 0
  isSOS_mult S := by
    split_ifs
    exacts [IsSOS.one, IsSOS.zero]
  degree_le S hS := by
    split_ifs at hS ⊢ with h
    · subst h
      simp
    · exact absurd rfl hS
  eq_sum := by
    classical
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro S _ hS
      simp [hS]
    · simp

/-- The term of `Proof.mul` for a pair of sets of constraints. -/
noncomputable def mulTerm {g₁ g₂ : MvPolynomial σ K} {k₁ k₂ : ℕ} (P₁ : Proof A g₁ k₁)
    (P₂ : Proof A g₂ k₂) (x : Finset (Fin A.length) × Finset (Fin A.length)) :
    MvPolynomial σ K :=
  P₁.mult x.1 * P₂.mult x.2 * A.prod (x.1 ∩ x.2) ^ 2

/-- **Product of proofs**: from degree-`k₁` and degree-`k₂` proofs of `g₁ ≥ 0` and `g₂ ≥ 0`, a
degree-`(k₁ + k₂)` proof of `g₁ g₂ ≥ 0`. The multiplier of a set `U` collects the products of
multipliers of all pairs `(S₁, S₂)` with `S₁ ∆ S₂ = U`, times the square of the constraints in
`S₁ ∩ S₂`. -/
noncomputable def mul {g₁ g₂ : MvPolynomial σ K} {k₁ k₂ : ℕ} (P₁ : Proof A g₁ k₁)
    (P₂ : Proof A g₂ k₂) : Proof A (g₁ * g₂) (k₁ + k₂) where
  mult U := by
    classical
    exact ∑ x ∈ Finset.univ ×ˢ Finset.univ with symmDiff x.1 x.2 = U, mulTerm P₁ P₂ x
  isSOS_mult U := by
    classical
    refine IsSOS.sum _ fun x _ ↦ ?_
    exact ((P₁.isSOS_mult x.1).mul (P₂.isSOS_mult x.2)).mul (IsSOS.sq _)
  degree_le U hU := by
    classical
    -- Every nonzero term has degree at most `k₁ + k₂ - deg U`, and some term is nonzero.
    have hterm : ∀ x ∈ (Finset.univ ×ˢ Finset.univ).filter (fun x ↦ symmDiff x.1 x.2 = U),
        mulTerm P₁ P₂ x ≠ 0 → (mulTerm P₁ P₂ x).totalDegree + A.degree U ≤ k₁ + k₂ := by
      intro x hx hne
      rw [Finset.mem_filter] at hx
      have h₁ : P₁.mult x.1 ≠ 0 := fun h ↦ hne (by simp [mulTerm, h])
      have h₂ : P₂.mult x.2 ≠ 0 := fun h ↦ hne (by simp [mulTerm, h])
      have d₁ := P₁.degree_le x.1 h₁
      have d₂ := P₂.degree_le x.2 h₂
      have hsum := A.degree_add_degree x.1 x.2
      have hprod := A.totalDegree_prod_le (x.1 ∩ x.2)
      have hdeg : (mulTerm P₁ P₂ x).totalDegree ≤
          (P₁.mult x.1).totalDegree + (P₂.mult x.2).totalDegree +
            2 * (A.prod (x.1 ∩ x.2)).totalDegree := by
        unfold mulTerm
        refine (totalDegree_mul _ _).trans ?_
        have := totalDegree_mul (P₁.mult x.1) (P₂.mult x.2)
        have := totalDegree_pow (A.prod (x.1 ∩ x.2)) 2
        omega
      rw [← hx.2]
      omega
    obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hU
    have hxU := hterm x hx hne
    refine Nat.le_sub_iff_add_le (by omega) |>.1 ?_
    refine totalDegree_finsetSum_le fun y hy ↦ ?_
    by_cases hy0 : mulTerm P₁ P₂ y = 0
    · simp [hy0]
    · have := hterm y hy hy0
      omega
  eq_sum := by
    classical
    conv_lhs => rw [P₁.eq_sum, P₂.eq_sum, Finset.sum_mul_sum, ← Finset.sum_product',
      ← Finset.sum_fiberwise (Finset.univ ×ˢ Finset.univ) (fun x ↦ symmDiff x.1 x.2)]
    refine Finset.sum_congr rfl fun U _ ↦ ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [Finset.mem_filter] at hx
    rw [← hx.2, mulTerm]
    linear_combination (P₁.mult x.1 * P₂.mult x.2) * A.prod_mul_prod x.1 x.2

end Proof

variable [Algebra K ℝ]

/-- From `A ⊢[k₁] g₁` and `A ⊢[k₂] g₂`, `A ⊢[k₁ + k₂] g₁ g₂`. -/
theorem Derives.mul {A : System σ K} {g₁ g₂ : MvPolynomial σ K} {k₁ k₂ : ℕ}
    (h₁ : Derives A k₁ g₁) (h₂ : Derives A k₂ g₂) : Derives A (k₁ + k₂) (g₁ * g₂) :=
  ⟨h₁.some.mul h₂.some⟩

theorem Derives.weaken {A : System σ K} {g : MvPolynomial σ K} {k k' : ℕ} (h : Derives A k g)
    (hk : k ≤ k') : Derives A k' g :=
  ⟨h.some.weaken hk⟩

/-- If every `g j` (`j ∈ T`) has a degree-`k` proof from `A`, their product has a proof of degree
`|T| k`. -/
theorem Derives.prod {A : System σ K} {ι : Type*} (T : Finset ι) {g : ι → MvPolynomial σ K}
    {k : ℕ} (h : ∀ j ∈ T, Derives A k (g j)) : Derives A (T.card * k) (∏ j ∈ T, g j) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨by simpa using Proof.one A⟩
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have := (h a (Finset.mem_insert_self a T)).mul
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
    exact this.weaken (by rw [Nat.succ_mul]; omega)

theorem Derives.zero (A : System σ K) (k : ℕ) : Derives A k 0 := ⟨Proof.zero A k⟩

theorem Derives.ofIsSOS (A : System σ K) {p : MvPolynomial σ K} (hp : IsSOS p) {k : ℕ}
    (hdeg : p.totalDegree ≤ k) : Derives A k p :=
  ⟨Proof.ofIsSOS A hp hdeg⟩

theorem Derives.assumption (A : System σ K) (i : Fin A.length) {k : ℕ}
    (hdeg : (A.get i).totalDegree ≤ k) : Derives A k (A.get i) :=
  ⟨Proof.assumption A i hdeg⟩

theorem Derives.add {A : System σ K} {g₁ g₂ : MvPolynomial σ K} {k : ℕ} (h₁ : Derives A k g₁)
    (h₂ : Derives A k g₂) : Derives A k (g₁ + g₂) :=
  ⟨h₁.some.add h₂.some⟩

theorem Derives.mulSOS {A : System σ K} {q : MvPolynomial σ K} (hq : IsSOS q)
    {g : MvPolynomial σ K} {k : ℕ} (h : Derives A k g) : Derives A (q.totalDegree + k) (q * g) :=
  ⟨h.some.mulSOS hq⟩

/-- A finite sum of polynomials with degree-`k` proofs has a degree-`k` proof. -/
theorem Derives.sum {A : System σ K} {ι : Type*} (T : Finset ι) {g : ι → MvPolynomial σ K}
    {k : ℕ} (h : ∀ j ∈ T, Derives A k (g j)) : Derives A k (∑ j ∈ T, g j) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using Derives.zero A k
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a T)).add (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-- **Equality constraints.** If `A` contains both `h ≥ 0` (at `i`) and `-h ≥ 0` (at `j`),
then `A` proves `q h ≥ 0` for every polynomial `q`, in degree `2 deg q + deg h`, since
`q h = ((q + 1) / 2)² h + ((q - 1) / 2)² (-h)`. -/
theorem Derives.mul_eq {A : System σ K} {i j : Fin A.length}
    {h : MvPolynomial σ K} (hi : A.get i = h) (hj : A.get j = -h) (q : MvPolynomial σ K) :
    Derives A (2 * q.totalDegree + h.totalDegree) (q * h) := by
  have h2 : (2 : K) ≠ 0 := fun h0 ↦ by
    have := congrArg (algebraMap K ℝ) h0
    rw [map_ofNat, map_zero] at this
    norm_num at this
  set a := C (1 / 2 : K) * (q + 1)
  set b := C (1 / 2 : K) * (q - 1)
  have hda : a.totalDegree ≤ q.totalDegree := by
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_add _ _).trans (max_le le_rfl (by simp))
  have hdb : b.totalDegree ≤ q.totalDegree := by
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_sub _ _).trans (max_le le_rfl (by simp))
  have hsq : ∀ p : MvPolynomial σ K, p.totalDegree ≤ q.totalDegree →
      (p ^ 2).totalDegree ≤ 2 * q.totalDegree := fun p hp ↦
    (totalDegree_pow p 2).trans (by omega)
  have ha := (Derives.assumption A i (k := h.totalDegree) (by rw [hi])).mulSOS (IsSOS.sq a)
  have hb := (Derives.assumption A j (k := h.totalDegree)
    (by rw [hj, totalDegree_neg])).mulSOS (IsSOS.sq b)
  have hsum := (ha.weaken (k' := 2 * q.totalDegree + h.totalDegree)
    (by have := hsq a hda; omega)).add
    (hb.weaken (k' := 2 * q.totalDegree + h.totalDegree) (by have := hsq b hdb; omega))
  have hc : (C (1 / 2 : K) * C (1 / 2) * 4 : MvPolynomial σ K) = 1 := by
    have : (1 / 2 : K) * (1 / 2) * 4 = 1 := by
      field_simp
      norm_num
    rw [show (4 : MvPolynomial σ K) = C 4 from (map_ofNat C 4).symm, ← C_mul, ← C_mul, this,
      C_1]
  have heq : a ^ 2 * A.get i + b ^ 2 * A.get j = q * h := by
    rw [hi, hj]
    simp only [a, b]
    linear_combination (q * h) * hc
  rwa [heq] at hsum

/-! ### Substitution -/

/-- Ring homomorphisms preserve sums of squares. -/
theorem isSumSq_map {R S F : Type*} [CommSemiring R] [CommSemiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) {s : R} (hs : IsSumSq s) : IsSumSq (f s) := by
  induction hs with
  | zero => simp
  | sq_add a _ ih =>
    rw [map_add, map_mul]
    exact IsSumSq.sq_add _ ih

/-- Substituting polynomials of degree at most `e` for the variables multiplies the degree by at
most `e`. -/
theorem totalDegree_aeval_le {τ R : Type*} [CommSemiring R] (φ : σ → MvPolynomial τ R) {e : ℕ}
    (hφ : ∀ j, (φ j).totalDegree ≤ e) (p : MvPolynomial σ R) :
    (aeval φ p).totalDegree ≤ p.totalDegree * e := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun m hm ↦ ?_
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  have hm' : (m.sum fun _ e ↦ e) ≤ p.totalDegree := le_totalDegree hm
  calc ∑ j ∈ m.support, (φ j ^ m j).totalDegree ≤ ∑ j ∈ m.support, m j * e :=
        Finset.sum_le_sum fun j _ ↦ (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hφ j))
    _ = (m.sum fun _ e ↦ e) * e := by rw [Finsupp.sum, Finset.sum_mul]
    _ ≤ p.totalDegree * e := Nat.mul_le_mul_right _ hm'

/-- Passing to real coefficients commutes with substitution. -/
theorem toReal_aeval {τ : Type*} (φ : σ → MvPolynomial τ K) (p : MvPolynomial σ K) :
    toReal (aeval φ p) = aeval (fun j ↦ toReal (φ j)) (toReal p) := by
  have := congrArg (fun F : MvPolynomial σ K →+* MvPolynomial τ ℝ ↦ F p)
    (MvPolynomial.ringHom_ext (f := (map (algebraMap K ℝ)).comp (aeval φ).toRingHom)
      (g := (aeval (fun j ↦ toReal (φ j))).toRingHom.comp (map (algebraMap K ℝ)))
      (fun c ↦ by simp [toReal]) (fun j ↦ by simp [toReal]))
  simpa [toReal] using this

theorem IsSOS.aeval {τ : Type*} {p : MvPolynomial σ K} (hp : IsSOS p)
    (φ : σ → MvPolynomial τ K) : IsSOS (aeval φ p) := by
  unfold IsSOS at hp ⊢
  rw [toReal_aeval]
  exact isSumSq_map _ hp

/-- **Substitution**: replacing each variable `j` by a polynomial `φ j` of degree at most `e` turns
a degree-`k` proof that `A` implies `g ≥ 0` into a degree-`k e` proof that `A[φ]` implies
`g[φ] ≥ 0`. -/
noncomputable def Proof.subst {τ : Type*} {A : System σ K} {g : MvPolynomial σ K} {k : ℕ}
    (P : Proof A g k) (φ : σ → MvPolynomial τ K) {e : ℕ} (hφ : ∀ j, (φ j).totalDegree ≤ e) :
    Proof (A.map (aeval φ)) (aeval φ g) (k * e) := by
  classical
  -- The constraints of the substituted system are indexed like those of `A`.
  let c : Fin (A.map (aeval φ)).length ≃ Fin A.length := finCongr (List.length_map _)
  have hget : ∀ i, (A.map (aeval φ)).get i = aeval φ (A.get (c i)) := fun i ↦ by
    simp [c, List.get_eq_getElem]
  have hprod : ∀ S, System.prod (A.map (aeval φ)) S = aeval φ (A.prod (S.map c.toEmbedding)) :=
    fun S ↦ by simp [System.prod, map_prod, Finset.prod_map, c]
  have hdeg : ∀ S, System.degree (A.map (aeval φ)) S ≤ A.degree (S.map c.toEmbedding) * e :=
    fun S ↦ by
      simp only [System.degree, Finset.sum_map, Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ ↦ by rw [hget]; exact totalDegree_aeval_le φ hφ _
  exact
  { mult := fun S ↦ aeval φ (P.mult (S.map c.toEmbedding))
    isSOS_mult := fun S ↦ (P.isSOS_mult _).aeval φ
    degree_le := fun S hS ↦ by
      have hS' : P.mult (S.map c.toEmbedding) ≠ 0 := fun h ↦ hS (by rw [h, map_zero])
      have h₁ := P.degree_le _ hS'
      have h₂ := totalDegree_aeval_le φ hφ (P.mult (S.map c.toEmbedding))
      have h₃ := hdeg S
      calc _ ≤ (P.mult (S.map c.toEmbedding)).totalDegree * e +
            A.degree (S.map c.toEmbedding) * e := Nat.add_le_add h₂ h₃
        _ = ((P.mult (S.map c.toEmbedding)).totalDegree + A.degree (S.map c.toEmbedding)) * e :=
            by ring
        _ ≤ k * e := Nat.mul_le_mul_right e h₁
    eq_sum := by
      conv_lhs => rw [P.eq_sum, map_sum]
      refine Fintype.sum_equiv c.finsetCongr.symm _ _ fun S ↦ ?_
      have hS : (c.finsetCongr.symm S).map c.toEmbedding = S := by
        rw [← Equiv.finsetCongr_apply, Equiv.apply_symm_apply]
      rw [hprod, hS, map_mul] }

theorem Derives.subst {τ : Type*} {A : System σ K} {g : MvPolynomial σ K} {k : ℕ}
    (h : Derives A k g) (φ : σ → MvPolynomial τ K) {e : ℕ} (hφ : ∀ j, (φ j).totalDegree ≤ e) :
    Derives (A.map (aeval φ)) (k * e) (aeval φ g) :=
  ⟨h.some.subst φ hφ⟩

/-! ### Composition -/

/-- **Composition.** If every constraint of `B` has a degree-`k` proof from `A`, and `g ≥ 0` has a
degree-`k'` proof from `B`, whose constraints are all nonconstant, then `g ≥ 0` has a proof from
`A` of degree `k' max k 1`. -/
theorem Derives.trans {A B : System σ K} {k k' : ℕ} (hAB : A.Entails B k)
    (hB : ∀ j, (B.get j).totalDegree ≠ 0) {g : MvPolynomial σ K} (hg : Derives B k' g) :
    Derives A (k' * max k 1) g := by
  classical
  obtain ⟨P⟩ := hg
  rw [P.eq_sum]
  refine Derives.sum _ fun T _ ↦ ?_
  by_cases hT : P.mult T = 0
  · rw [hT, zero_mul]
    exact Derives.zero A _
  -- The product of the constraints in `T` has a proof of degree `|T| k` from `A`, and
  -- `|T| ≤ ∑ j ∈ T, deg g_j` since every constraint of `B` is nonconstant.
  have hprod : Derives A (T.card * k) (B.prod T) :=
    Derives.prod T fun j _ ↦ hAB _ (List.get_mem B j)
  have hdeg := P.degree_le T hT
  have hcard : T.card ≤ B.degree T := by
    rw [Finset.card_eq_sum_ones, System.degree]
    exact Finset.sum_le_sum fun j _ ↦ Nat.one_le_iff_ne_zero.2 (hB j)
  refine (hprod.mulSOS (P.isSOS_mult T)).weaken ?_
  calc (P.mult T).totalDegree + T.card * k
      ≤ (P.mult T).totalDegree * max k 1 + T.card * max k 1 :=
        Nat.add_le_add (Nat.le_mul_of_pos_right _ (by omega))
          (Nat.mul_le_mul_left _ (le_max_left _ _))
    _ = ((P.mult T).totalDegree + T.card) * max k 1 := by ring
    _ ≤ k' * max k 1 := Nat.mul_le_mul_right _ (by omega)

end SoS
