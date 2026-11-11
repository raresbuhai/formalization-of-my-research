module

public import BHSV25.Hard.Design

/-!
# The template of a design, by arithmetic on cell numbers

The cells of `BHSV25.Hard.Design.template D a` are numbered `u = τ + |types| · x`, for the
number `τ` of the type and the number `x` of the point of `Γ₀^r`, written in base `2 · 4^a` with
digits `g = Y + 2^a X + 4^a b` for the points `(b, x, y)` of `Γ₀` (`BHSV25.Hard.Design.eqv`).
This file computes the template from these numbers, as a machine does:

* the digits of `x` and their parts (`BHSV25.Hard.Design.dig`, `.dB`, `.dX`, `.dY`);
* the bent function of the sum of two points, the parity of `[b ≠ b']` plus the number of
  coordinates `i` with `x_i ≠ x'_i` and `y_i ≠ y'_i` (`BHSV25.Hard.Design.bentN`), and `hval` of
  the sum (`BHSV25.Hard.Design.hvalN`, `BHSV25.Hard.Design.hval_add_eq`);
* the adjacency and the correction of the template (`BHSV25.Hard.Design.T_eq`,
  `BHSV25.Hard.Design.W_eq`), from the group, the densities and the correction of the types.
-/

@[expose] public section

namespace BHSV25.Hard.Design

open Finset Cayley

/-- The base `2 · 4^a` of the numbering of `Γ₀^r`. -/
abbrev base (a : ℕ) : ℕ := 2 * (2 ^ a * 2 ^ a)

/-- The digit `l` of `x` in base `2 · 4^a`. -/
def dig (a l x : ℕ) : ℕ := x / base a ^ l % base a

/-- The parts of a digit `g = Y + 2^a X + 4^a b`. -/
def dB (a g : ℕ) : ℕ := g / (2 ^ a * 2 ^ a)

def dX (a g : ℕ) : ℕ := g % (2 ^ a * 2 ^ a) / 2 ^ a

def dY (a g : ℕ) : ℕ := g % (2 ^ a * 2 ^ a) % 2 ^ a

/-- The bent function of the sum of the points of `Γ₀` numbered `g` and `g'`. -/
def bentN (a g g' : ℕ) : ℕ :=
  ((if dB a g = dB a g' then 0 else 1) +
    (List.range a).countP fun i ↦ decide ((dX a g).testBit i ≠ (dX a g').testBit i ∧
      (dY a g).testBit i ≠ (dY a g').testBit i)) % 2

/-- `hval (s + s')` from the numbers `x, x'` of `s, s' ∈ Γ₀^r`. -/
def hvalN (a r x x' : ℕ) : ℕ :=
  ((List.range r).map fun l ↦ bentN a (dig a l x) (dig a l x') * 2 ^ l).sum

/-! ### The parts of a point of `Γ₀` -/

theorem gamEquiv_val (a : ℕ) (w : Gam0 a) :
    (gamEquiv a w : ℕ) = ((finFunctionFinEquiv w.2.2 : Fin (2 ^ a)) : ℕ) +
      2 ^ a * (finFunctionFinEquiv w.2.1 : Fin (2 ^ a)) +
      2 ^ a * 2 ^ a * w.1.val := by
  change ((finProdFinEquiv ((w.1 : Fin 2), finProdFinEquiv
    ((finFunctionFinEquiv w.2.1 : Fin (2 ^ a)), (finFunctionFinEquiv w.2.2 : Fin (2 ^ a)))) :
      Fin (2 * (2 ^ a * 2 ^ a))) : ℕ) = _
  rw [finProdFinEquiv_apply_val]
  simp only
  rw [finProdFinEquiv_apply_val]
  simp only [ZMod.val]

theorem dB_gamEquiv (a : ℕ) (w : Gam0 a) : dB a (gamEquiv a w) = w.1.val := by
  rw [dB, gamEquiv_val]
  have hY := (finFunctionFinEquiv w.2.2 : Fin (2 ^ a)).isLt
  have hX := (finFunctionFinEquiv w.2.1 : Fin (2 ^ a)).isLt
  have hlt : ((finFunctionFinEquiv w.2.2 : Fin (2 ^ a)) : ℕ) +
      2 ^ a * (finFunctionFinEquiv w.2.1 : Fin (2 ^ a)) < 2 ^ a * 2 ^ a := by
    nlinarith
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]

theorem rem_gamEquiv (a : ℕ) (w : Gam0 a) :
    (gamEquiv a w : ℕ) % (2 ^ a * 2 ^ a) =
      ((finFunctionFinEquiv w.2.2 : Fin (2 ^ a)) : ℕ) +
        2 ^ a * (finFunctionFinEquiv w.2.1 : Fin (2 ^ a)) := by
  rw [gamEquiv_val]
  have hY := (finFunctionFinEquiv w.2.2 : Fin (2 ^ a)).isLt
  have hX := (finFunctionFinEquiv w.2.1 : Fin (2 ^ a)).isLt
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by nlinarith)]

theorem dX_gamEquiv (a : ℕ) (w : Gam0 a) :
    dX a (gamEquiv a w) = finFunctionFinEquiv w.2.1 := by
  rw [dX, rem_gamEquiv]
  have hY := (finFunctionFinEquiv w.2.2 : Fin (2 ^ a)).isLt
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hY, zero_add]

theorem dY_gamEquiv (a : ℕ) (w : Gam0 a) :
    dY a (gamEquiv a w) = finFunctionFinEquiv w.2.2 := by
  rw [dY, rem_gamEquiv]
  have hY := (finFunctionFinEquiv w.2.2 : Fin (2 ^ a)).isLt
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hY]

/-- The bits of the binary number with digits `x`. -/
theorem testBit_finFunctionFinEquiv {a : ℕ} (x : Fin a → Fin 2) (i : Fin a) :
    ((finFunctionFinEquiv x : Fin (2 ^ a)) : ℕ).testBit i = decide (x i = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv x) i
  rw [Equiv.symm_apply_apply] at h
  rw [← h]
  rcases Fin.exists_fin_two.1 ⟨x i, rfl⟩ with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

/-! ### The bent function of a sum -/

theorem zmod2_add_eq (c c' : ZMod 2) : c + c' = if c = c' then 0 else 1 := by
  fin_cases c <;> fin_cases c' <;> decide

theorem zmod2_mul_add (c₁ c₁' c₂ c₂' : ZMod 2) :
    (c₁ + c₁') * (c₂ + c₂') = if c₁ ≠ c₁' ∧ c₂ ≠ c₂' then 1 else 0 := by
  fin_cases c₁ <;> fin_cases c₁' <;> fin_cases c₂ <;> fin_cases c₂' <;> decide

theorem countP_range_eq {a : ℕ} (p : ℕ → Bool) :
    (List.range a).countP p = (univ.filter fun i : Fin a ↦ p i = true).card := by
  have h1 : (univ.filter fun i : Fin a ↦ p i = true).card =
      ((range a).filter fun i ↦ p i).card := by
    rw [← card_map ⟨Fin.val, Fin.val_injective⟩]
    congr 1
    ext j
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk, mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i.2, hi⟩
    · rintro ⟨hj, hp⟩; exact ⟨⟨j, hj⟩, hp, rfl⟩
  rw [h1, List.countP_eq_length_filter]
  rfl

/-- **The bent function of a sum**, from the numbers of the two points. -/
theorem bent_add_val (a : ℕ) (w w' : Gam0 a) :
    (bent (w + w')).val = bentN a (gamEquiv a w) (gamEquiv a w') := by
  unfold bent bentN
  rw [dB_gamEquiv, dB_gamEquiv, dX_gamEquiv, dX_gamEquiv, dY_gamEquiv, dY_gamEquiv]
  have hcount : (List.range a).countP (fun i ↦ decide
      (((finFunctionFinEquiv w.2.1 : Fin (2 ^ a)) : ℕ).testBit i ≠
        ((finFunctionFinEquiv w'.2.1 : Fin (2 ^ a)) : ℕ).testBit i ∧
      ((finFunctionFinEquiv w.2.2 : Fin (2 ^ a)) : ℕ).testBit i ≠
        ((finFunctionFinEquiv w'.2.2 : Fin (2 ^ a)) : ℕ).testBit i)) =
      (univ.filter fun i : Fin a ↦ w.2.1 i ≠ w'.2.1 i ∧ w.2.2 i ≠ w'.2.2 i).card := by
    rw [countP_range_eq]
    congr 1
    refine filter_congr fun i _ ↦ ?_
    rw [testBit_finFunctionFinEquiv (w.2.1 : Fin a → Fin 2),
      testBit_finFunctionFinEquiv (w'.2.1 : Fin a → Fin 2),
      testBit_finFunctionFinEquiv (w.2.2 : Fin a → Fin 2),
      testBit_finFunctionFinEquiv (w'.2.2 : Fin a → Fin 2)]
    have hc : ∀ c c' : Fin 2, (decide (c = 1) ≠ decide (c' = 1) ↔ c ≠ c') := by decide
    rw [decide_eq_true_iff]
    exact Iff.and (hc (w.2.1 i) (w'.2.1 i)) (hc (w.2.2 i) (w'.2.2 i))
  rw [hcount]
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [zmod2_add_eq w.1 w'.1]
  simp_rw [zmod2_mul_add]
  rw [Finset.sum_boole]
  have hb : w.1 = w'.1 ↔ w.1.val = w'.1.val := (ZMod.val_injective 2).eq_iff.symm
  by_cases h : w.1 = w'.1
  · rw [ite_eq_left h, ite_eq_left (hb.1 h), zero_add, zero_add, ZMod.val_natCast]
  · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (hb.2 h')), ← Nat.cast_one (R := ZMod 2),
      ← Nat.cast_add, ZMod.val_natCast]

/-! ### `hval` of a sum -/

theorem list_range_sum' {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ((List.range n).map g).sum = ∑ j ∈ range n, g j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- The digits of the number of `s ∈ Γ₀^r` are the numbers of its coordinates. -/
theorem dig_gamrEquiv (a r : ℕ) (s : Fin r → Gam0 a) (l : Fin r) :
    dig a l (gamrEquiv a r s) = gamEquiv a (s l) := by
  unfold dig gamrEquiv
  have h := finFunctionFinEquiv_symm_apply_val
    (finFunctionFinEquiv (fun l ↦ gamEquiv a (s l))) l
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

/-- **`hval` of a sum**, from the numbers of the two points of `Γ₀^r`. -/
theorem hval_add_eq (a r : ℕ) (s s' : Fin r → Gam0 a) :
    hval (s + s') = hvalN a r (gamrEquiv a r s) (gamrEquiv a r s') := by
  unfold hval hvalN
  rw [list_range_sum', ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun l _ ↦ ?_
  rw [Pi.add_apply, bent_add_val, dig_gamrEquiv, dig_gamrEquiv]

/-! ### The template -/

variable (D : Design) (a : ℕ)

/-- **The adjacency of the template** from the cell numbers: the groups of the types differ, and
`hvalN` of the points is below the density of the groups. -/
theorem T_eq (u u' : Fin (Fintype.card (D.Cell a))) :
    (D.template a).T u u' =
      (decide (D.gr ((D.eqv a).symm u).1 ≠ D.gr ((D.eqv a).symm u').1) &&
        decide (hvalN a D.r (u / Fintype.card D.Ty) (u' / Fintype.card D.Ty) <
          D.q (D.gr ((D.eqv a).symm u).1) (D.gr ((D.eqv a).symm u').1))) := by
  simp only [Tc, hval_add_eq, eqv_symm_snd, Bool.decide_and]

/-- **The correction of the template** from the cell numbers. -/
theorem W_eq (u u' : Fin (Fintype.card (D.Cell a))) :
    (D.template a).W u u' = if u / Fintype.card D.Ty = u' / Fintype.card D.Ty then
      D.W0 ((D.eqv a).symm u).1 ((D.eqv a).symm u').1 else 0 := by
  simp only [Wc]
  have h : ((D.eqv a).symm u).2 = ((D.eqv a).symm u').2 ↔
      u / Fintype.card D.Ty = u' / Fintype.card D.Ty := by
    rw [← eqv_symm_snd, ← eqv_symm_snd, Fin.val_inj, (gamrEquiv a D.r).apply_eq_iff_eq]
  by_cases hs : ((D.eqv a).symm u).2 = ((D.eqv a).symm u').2
  · rw [ite_eq_left hs, ite_eq_left (h.1 hs)]
  · rw [ite_eq_right hs, ite_eq_right (fun h' ↦ hs (h.2 h'))]

end BHSV25.Hard.Design
