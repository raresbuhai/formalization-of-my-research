module

public import BGHKLMM26.IntGap.KS
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Boolean functions modulo characters (Khot–Vishnoi)

The objects of Khot and Vishnoi's Unique Games integrality gap [KV15, Section 3], over `ZMod 2`:
points `x ∈ Pt k = {0,1}^k`, Boolean functions `f ∈ Fn k` (truth tables, a group under pointwise
addition), labels `s ∈ Lab k = {0,1}^k` and the characters `χ_s(x) = Σᵢ sᵢ xᵢ`
(`BGHKLMM26.IntGap.chi`). The characters form a subgroup `BGHKLMM26.IntGap.walsh` with `2^k`
elements, and its cosets are the classes `BGHKLMM26.IntGap.Cls k` (the vertices of the instance),
each with a chosen representative `BGHKLMM26.IntGap.rep`; the functions `rep P + χ_s` are the
labels of `P`.

The correlation `corr f g = 2^{-k} Σₓ (-1)^{f x - g x}` (`BGHKLMM26.IntGap.corr`) is the inner
product of the truth tables, and `tvec f` (`BGHKLMM26.IntGap.tvec`) is the tensor square of the
normalized truth table, with `⟨tvec f, tvec g⟩ = corr f g ²`. The tuples
`T_{P,s} = tvec (rep P + χ_s)` are symmetric orthonormal tuples (`BGHKLMM26.IntGap.kvTup`): the
characters are orthonormal, squares are nonnegative, and adding `χ_l` to both functions does not
change the correlation.
-/

@[expose] public section

namespace BGHKLMM26.IntGap

open scoped RealInnerProductSpace

/-- Points of `{0,1}^k`. -/
abbrev Pt (k : ℕ) := Fin k → ZMod 2

/-- Boolean functions on `{0,1}^k`, a group under pointwise addition. -/
abbrev Fn (k : ℕ) := Pt k → ZMod 2

/-- Labels: the indices of the characters. -/
abbrev Lab (k : ℕ) := Fin k → ZMod 2

variable {k : ℕ}

/-- The character `χ_s(x) = Σᵢ sᵢ xᵢ`. -/
def chi (s : Lab k) : Fn k := fun x ↦ ∑ i, s i * x i

/-- The characters as an additive map. -/
def chiHom (k : ℕ) : Lab k →+ Fn k where
  toFun := chi
  map_zero' := by funext x; simp [chi]
  map_add' s t := by funext x; simp [chi, add_mul, Finset.sum_add_distrib]

/-- The subgroup of characters. -/
def walsh (k : ℕ) : AddSubgroup (Fn k) := (chiHom k).range

/-- **The classes**: Boolean functions modulo characters. -/
abbrev Cls (k : ℕ) := Fn k ⧸ walsh k

noncomputable instance (k : ℕ) : Fintype (Cls k) := Fintype.ofFinite _

/-- The chosen representative of a class. -/
noncomputable def rep (P : Cls k) : Fn k := Quotient.out P

/-- A bit as a sign: `0 ↦ 1`, `1 ↦ -1`. -/
def sgn (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

/-- The correlation `2^{-k} Σₓ (-1)^{f x - g x}` of two Boolean functions. -/
noncomputable def corr (f g : Fn k) : ℝ := (∑ x, sgn (f x - g x)) / 2 ^ k

/-- The tensor square of the normalized truth table of `f`. -/
noncomputable def tvec (f : Fn k) : EuclideanSpace ℝ (Pt k × Pt k) :=
  WithLp.toLp 2 fun p ↦ sgn (f p.1) * sgn (f p.2) / 2 ^ k

/-- A bit is `0` or `1`. -/
theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

/-- Signs multiply: `(-1)^{a - b} = (-1)^a (-1)^b`. -/
theorem sgn_sub (a b : ZMod 2) : sgn (a - b) = sgn a * sgn b := by
  have h1 : (1 : ZMod 2) ≠ 0 := by decide
  have h2 : (0 : ZMod 2) - 1 = 1 := by decide
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    simp [sgn, h1, h2]

/-- Flipping a bit flips its sign. -/
theorem sgn_add_one (a : ZMod 2) : sgn (a + 1) = -sgn a := by
  have h1 : (1 : ZMod 2) ≠ 0 := by decide
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod_two_cases a with rfl | rfl <;> simp [sgn, h1, h2]

/-- Signs have absolute value `1`. -/
theorem abs_sgn (a : ZMod 2) : |sgn a| = 1 := by
  unfold sgn; split_ifs <;> simp

theorem inner_tvec (f g : Fn k) : ⟪tvec f, tvec g⟫ = corr f g ^ 2 := by
  simp only [tvec, corr, PiLp.inner_apply, Real.inner_apply, sgn_sub]
  rw [div_pow, sq, Finset.sum_mul_sum, Finset.sum_div, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  ring

theorem chi_add (s t : Lab k) : chi (s + t) = chi s + chi t := (chiHom k).map_add s t

/-- The character `χ_s` at the `i`-th unit vector is `sᵢ`. -/
theorem chi_single (s : Lab k) (i : Fin k) : chi s (Pi.single i 1) = s i := by
  simp [chi, Pi.single_apply]

/-- Characters are additive in the point. -/
theorem chi_apply_add (s : Lab k) (x y : Pt k) : chi s (x + y) = chi s x + chi s y := by
  simp [chi, mul_add, Finset.sum_add_distrib]

theorem chi_injective : Function.Injective (chi (k := k)) := by
  intro s t h
  funext i
  rw [← chi_single s i, ← chi_single t i, h]

theorem mem_walsh_iff (g : Fn k) : g ∈ walsh k ↔ ∃ s, g = chi s := by
  simp only [walsh, AddMonoidHom.mem_range, eq_comm (a := g)]
  rfl

/-- Characters are additive in the label. -/
theorem chi_sub (s t : Lab k) : chi (s - t) = chi s - chi t := (chiHom k).map_sub s t

/-- The trivial character. -/
theorem chi_zero : chi (0 : Lab k) = 0 := (chiHom k).map_zero

/-- A bit is nonzero iff adding one to it gives zero. -/
theorem zmod_two_add_one_eq_zero_iff (a : ZMod 2) : a + 1 = 0 ↔ a ≠ 0 := by
  revert a; decide

/-- Translating twice by the same point is the identity. -/
theorem pt_add_add_self (x y : Pt k) : x + y + y = x := by
  have h : ∀ a b : ZMod 2, a + b + b = a := by decide
  funext j; exact h (x j) (y j)

/-- A nonzero label has a coordinate equal to `1`. -/
theorem exists_eq_one_of_ne_zero {s : Lab k} (hs : s ≠ 0) : ∃ i, s i = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hs
  exact ⟨i, (zmod_two_cases (s i)).resolve_left hi⟩

/-- Translating by a unit vector `eᵢ` with `sᵢ = 1` flips `χ_s`. -/
theorem chi_add_single {s : Lab k} {i : Fin k} (hi : s i = 1) (x : Pt k) :
    chi s (x + Pi.single i 1) = chi s x + 1 := by
  rw [chi_apply_add, chi_single, hi]

/-- A nonzero character takes the value `1` on exactly half of the points. -/
theorem card_chi_ne_zero {s : Lab k} (hs : s ≠ 0) :
    (Finset.univ.filter fun x ↦ chi s x ≠ 0).card = 2 ^ k / 2 := by
  obtain ⟨i, hi⟩ := exists_eq_one_of_ne_zero hs
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x : Pt k ↦ chi s x ≠ 0)
  have heq : (Finset.univ.filter fun x ↦ chi s x ≠ 0).card =
      (Finset.univ.filter fun x ↦ ¬chi s x ≠ 0).card := by
    refine Finset.card_nbij' (· + Pi.single i 1) (· + Pi.single i 1) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [chi_add_single hi, not_not, zmod_two_add_one_eq_zero_iff]
      exact hx
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [chi_add_single hi, ne_eq, zmod_two_add_one_eq_zero_iff]
      exact hx
    · intro x _
      exact pt_add_add_self x _
    · intro x _
      exact pt_add_add_self x _
  have hN : (Finset.univ : Finset (Pt k)).card = 2 ^ k := by simp [ZMod.card]
  omega

/-- The representative of the class of `f` is `f + χ_s` for some `s`. -/
theorem exists_rep_eq (f : Fn k) : ∃ s : Lab k, rep (f : Cls k) = f + chi s := by
  have h : ((rep (f : Cls k) : Fn k) : Cls k) = f := QuotientAddGroup.out_eq' _
  obtain ⟨s, hs⟩ := (mem_walsh_iff _).1 (QuotientAddGroup.eq.1 h.symm)
  exact ⟨s, by rw [← hs]; abel⟩

theorem corr_comm (f g : Fn k) : corr f g = corr g f := by
  simp only [corr, sgn_sub, mul_comm]

theorem abs_corr_le (f g : Fn k) : |corr f g| ≤ 1 := by
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  rw [corr, abs_div, abs_of_pos hN, div_le_one hN]
  calc |∑ x, sgn (f x - g x)| ≤ ∑ x, |sgn (f x - g x)| := Finset.abs_sum_le_sum_abs _ _
    _ = 2 ^ k := by simp [abs_sgn, ZMod.card]

theorem corr_add_right (f g h : Fn k) : corr (f + h) (g + h) = corr f g := by
  simp [corr]

/-- **Character sums**: `Σₓ (-1)^{χ_s(x)} = 0` for `s ≠ 0`. -/
theorem sum_sgn_chi {s : Lab k} (hs : s ≠ 0) : ∑ x, sgn (chi s x) = 0 := by
  obtain ⟨i, hi⟩ := exists_eq_one_of_ne_zero hs
  have h := Equiv.sum_comp (Equiv.addRight (Pi.single i 1 : Pt k)) fun x ↦ sgn (chi s x)
  simp only [Equiv.coe_addRight, chi_add_single hi, sgn_add_one, Finset.sum_neg_distrib] at h
  linarith

/-- **Orthonormality of the characters**. -/
theorem corr_add_chi (f : Fn k) (s t : Lab k) :
    corr (f + chi s) (f + chi t) = if s = t then 1 else 0 := by
  have h : ∀ x, (f + chi s) x - (f + chi t) x = chi (s - t) x := by
    intro x; rw [chi_sub]; simp
  simp only [corr, h]
  split_ifs with hst
  · subst hst
    simp [chi_zero, sgn, ZMod.card]
  · rw [sum_sgn_chi (sub_ne_zero.2 hst), zero_div]

/-- Two functions that differ only on `Z` have correlation at least `1 - 2|Z|/2^k`. -/
theorem corr_ge_of_eqOn (f g : Fn k) (Z : Finset (Pt k)) (h : ∀ x, x ∉ Z → f x = g x) :
    1 - 2 * Z.card / 2 ^ k ≤ corr f g := by
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  have hle : ∀ x, 1 - 2 * (if x ∈ Z then (1 : ℝ) else 0) ≤ sgn (f x - g x) := by
    intro x
    by_cases hx : x ∈ Z
    · have := abs_le.1 (abs_sgn (f x - g x)).le
      simp only [hx, ↓reduceIte]; linarith
    · simp [hx, h x hx, sgn]
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) ↦ hle x
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.univ_inter] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, ZMod.card, Finset.prod_const,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  rw [corr, le_div_iff₀ hN, sub_mul, div_mul_cancel₀ _ hN.ne', one_mul]
  push_cast at hsum
  linarith

/-- **Khot and Vishnoi's tuples**: `T_{P,s} = tvec (rep P + χ_s)`. -/
noncomputable def kvTup (k : ℕ) : SymTuples (Cls k) (Lab k) (Pt k × Pt k) where
  vec P s := tvec (rep P + chi s)
  orth u i j := by
    rw [inner_tvec, corr_add_chi]
    split_ifs <;> norm_num
  nonneg u i v j := by rw [inner_tvec]; positivity
  shift u i v j l := by
    rw [inner_tvec, inner_tvec, chi_add, chi_add, ← add_assoc, ← add_assoc, corr_add_right]

end BGHKLMM26.IntGap
