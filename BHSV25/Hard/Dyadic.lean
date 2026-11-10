module

public import BHSV25.Hard.Cayley

/-!
# Pseudo-random sets of dyadic densities

The second half of the construction of `BHSV25/Hard/Cayley.lean`: pseudo-randomness
(`BHSV25.Hard.Cayley.PR`) of the level sets of the bent function, of products, of disjoint
unions, and so of the sets `{z ∈ Γ₀^r : hval z < q}` of density exactly `q / 2^r`
(`BHSV25.Hard.Cayley.pr_lt`, `BHSV25.Hard.Cayley.card_lt`).
-/

@[expose] public section

namespace BHSV25.Hard.Cayley

open Finset

variable {a : ℕ}

/-- `S` is **`(ρ, e)`-pseudo-random**:
`|∑_{x,y} X_x [x + y ∈ S] Y_y - ρ (∑ X)(∑ Y)| ≤ e (‖X‖² + ‖Y‖²)` for all `X, Y`. -/
def PR {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] (S : Γ → Prop) (ρ e : ℝ) : Prop :=
  ∀ X Y : Γ → ℝ, |∑ x, ∑ y, X x * ind (S (x + y)) * Y y - ρ * (∑ x, X x) * ∑ y, Y y| ≤
    e * (∑ x, X x ^ 2 + ∑ y, Y y ^ 2)

section General

variable {Γ : Type*} [AddCommGroup Γ] [Fintype Γ]

theorem PR.mono {S : Γ → Prop} {ρ e e' : ℝ} (h : PR S ρ e) (he : e ≤ e') : PR S ρ e' :=
  fun X Y ↦ (h X Y).trans (mul_le_mul_of_nonneg_right he (by positivity))

theorem PR.congr {S S' : Γ → Prop} {ρ e : ℝ} (h : PR S ρ e) (hS : ∀ z, S z ↔ S' z) :
    PR S' ρ e := by
  intro X Y
  have : ∀ z, ind (S' z) = ind (S z) := fun z ↦ congrArg ind (propext (hS z)).symm
  simp_rw [this]
  exact h X Y

/-- Disjoint unions of pseudo-random sets are pseudo-random. -/
theorem PR.or {S S' : Γ → Prop} {ρ ρ' e e' : ℝ} (h : PR S ρ e) (h' : PR S' ρ' e')
    (hdisj : ∀ z, ¬ (S z ∧ S' z)) : PR (fun z ↦ S z ∨ S' z) (ρ + ρ') (e + e') := by
  intro X Y
  have hind : ∀ z, ind (S z ∨ S' z) = ind (S z) + ind (S' z) := by
    intro z
    by_cases hz : S z
    · rw [ind_of (Or.inl hz), ind_of hz, ind_of_not (fun h'' ↦ hdisj z ⟨hz, h''⟩)]; ring
    · by_cases hz' : S' z
      · rw [ind_of (Or.inr hz'), ind_of_not hz, ind_of hz']; ring
      · rw [ind_of_not (by tauto), ind_of_not hz, ind_of_not hz']; ring
  have hsplit : ∑ x, ∑ y, X x * ind (S (x + y) ∨ S' (x + y)) * Y y - (ρ + ρ') * (∑ x, X x) *
      ∑ y, Y y = (∑ x, ∑ y, X x * ind (S (x + y)) * Y y - ρ * (∑ x, X x) * ∑ y, Y y) +
      (∑ x, ∑ y, X x * ind (S' (x + y)) * Y y - ρ' * (∑ x, X x) * ∑ y, Y y) := by
    simp_rw [hind, mul_add, add_mul, sum_add_distrib]
    ring
  rw [hsplit, add_mul]
  exact (abs_add_le _ _).trans (add_le_add (h X Y) (h' X Y))

end General

/-! ### The level sets of the bent function -/

theorem ind_bent_eq (c : ZMod 2) (w : Gam0 a) :
    ind (bent w = c) = (1 + sgn c * sgn (bent w)) / 2 := by
  by_cases h : bent w = c
  · rw [ind_of h, h, sgn_mul_self]; norm_num
  · rw [ind_of_not h]
    have : bent w = c + 1 := by
      rcases zmod2_cases c with rfl | rfl <;> rcases zmod2_cases (bent w) with h' | h' <;>
        simp_all [one_add_one_zmod2]
    rw [this, sgn_add, ← mul_assoc, sgn_mul_self, sgn_one]; norm_num

/-- **The level sets of the bent function are `(1/2, 2^a / 2)`-pseudo-random.** -/
theorem pr_bent (c : ZMod 2) : PR (fun w : Gam0 a ↦ bent w = c) (1 / 2) (2 ^ a / 2) := by
  intro X Y
  have h := abs_bil_sgn_le X Y
  have hrw : ∑ x, ∑ y, X x * ind (bent (x + y) = c) * Y y - 1 / 2 * (∑ x, X x) * ∑ y, Y y =
      sgn c / 2 * ∑ x, ∑ y, X x * sgn (bent (x + y)) * Y y := by
    have e : ∑ x, ∑ y, X x * ind (bent (x + y) = c) * Y y =
        ∑ x, ∑ y, (1 / 2 * (X x * Y y) + sgn c / 2 * (X x * sgn (bent (x + y)) * Y y)) :=
      sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ by rw [ind_bent_eq]; ring
    rw [e]
    simp only [sum_add_distrib, ← mul_sum]
    rw [← sum_mul]
    ring
  rw [hrw, abs_mul]
  have hs : |sgn c / 2| = 1 / 2 := by
    rcases zmod2_cases c with rfl | rfl <;> simp [sgn_zero, sgn_one, abs_div]
  rw [hs]
  linarith

/-! ### Products -/

section Cons

variable {r : ℕ}

theorem sum_cons {β : Type*} [AddCommMonoid β] (F : (Fin (r + 1) → Gam0 a) → β) :
    ∑ z, F z = ∑ w, ∑ z', F (Fin.cons w z') := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ ↦ Gam0 a).symm F (fun p ↦ F (Fin.cons p.1 p.2))
    (fun z ↦ by simp [Fin.consEquiv])

theorem cons_add_cons (w w' : Gam0 a) (z z' : Fin r → Gam0 a) :
    (Fin.cons w z : Fin (r + 1) → Gam0 a) + Fin.cons w' z' = Fin.cons (w + w') (z + z') := by
  funext i
  refine Fin.cases ?_ ?_ i <;> simp

/-- **Products of pseudo-random sets are pseudo-random**, in the form `Γ₀ × Γ₀^r = Γ₀^(r+1)`. -/
theorem pr_cons {f : Gam0 a → Prop} {g : (Fin r → Gam0 a) → Prop} {ρ₁ e₁ ρ₂ e₂ : ℝ}
    (hf : PR f ρ₁ e₁) (hg : PR g ρ₂ e₂) (he₁ : 0 ≤ e₁) :
    PR (fun z : Fin (r + 1) → Gam0 a ↦ f (z 0) ∧ g (Fin.tail z)) (ρ₁ * ρ₂)
      (e₂ * Fintype.card (Gam0 a) + |ρ₂| * e₁ * Fintype.card (Fin r → Gam0 a)) := by
  intro X Y
  -- the inner errors, for each pair of first coordinates
  have hin : ∀ w w', |∑ z, ∑ z', X (Fin.cons w z) * ind (g (z + z')) * Y (Fin.cons w' z') -
      ρ₂ * (∑ z, X (Fin.cons w z)) * ∑ z', Y (Fin.cons w' z')| ≤
      e₂ * (∑ z, X (Fin.cons w z) ^ 2 + ∑ z', Y (Fin.cons w' z') ^ 2) :=
    fun w w' ↦ hg _ _
  -- the outer error
  have hout := hf (fun w ↦ ∑ z, X (Fin.cons w z)) (fun w ↦ ∑ z, Y (Fin.cons w z))
  have hbil : ∑ x, ∑ y, X x * ind (f ((x + y) 0) ∧ g (Fin.tail (x + y))) * Y y =
      ∑ w, ∑ w', ind (f (w + w')) *
        ∑ z, ∑ z', X (Fin.cons w z) * ind (g (z + z')) * Y (Fin.cons w' z') := by
    have hpt : ∀ (w : Gam0 a) (z : Fin r → Gam0 a) (w' : Gam0 a) (z' : Fin r → Gam0 a),
        X (Fin.cons w z) * ind (f ((Fin.cons w z + Fin.cons w' z' : Fin (r + 1) → Gam0 a) 0) ∧
          g (Fin.tail (Fin.cons w z + Fin.cons w' z' : Fin (r + 1) → Gam0 a))) *
            Y (Fin.cons w' z') =
        ind (f (w + w')) * (X (Fin.cons w z) * ind (g (z + z')) * Y (Fin.cons w' z')) := by
      intro w z w' z'
      rw [cons_add_cons, Fin.cons_zero, Fin.tail_cons]
      by_cases h1 : f (w + w') <;> by_cases h2 : g (z + z')
      · rw [ind_of ⟨h1, h2⟩, ind_of h1, ind_of h2]; ring
      · rw [ind_of_not (fun h ↦ h2 h.2), ind_of h1, ind_of_not h2]; ring
      · rw [ind_of_not (fun h ↦ h1 h.1), ind_of_not h1]; ring
      · rw [ind_of_not (fun h ↦ h1 h.1), ind_of_not h1]; ring
    simp only [sum_cons, hpt, mul_sum]
    refine sum_congr rfl fun w _ ↦ ?_
    rw [sum_comm]
  have hX : ∑ z, X z = ∑ w, ∑ z, X (Fin.cons w z) := sum_cons _
  have hY : ∑ z, Y z = ∑ w, ∑ z, Y (Fin.cons w z) := sum_cons _
  have hid : ∑ x, ∑ y, X x * ind (f ((x + y) 0) ∧ g (Fin.tail (x + y))) * Y y -
      ρ₁ * ρ₂ * (∑ x, X x) * ∑ y, Y y =
      ∑ w, ∑ w', ind (f (w + w')) *
        (∑ z, ∑ z', X (Fin.cons w z) * ind (g (z + z')) * Y (Fin.cons w' z') -
          ρ₂ * (∑ z, X (Fin.cons w z)) * ∑ z', Y (Fin.cons w' z')) +
      ρ₂ * (∑ w, ∑ w', (∑ z, X (Fin.cons w z)) * ind (f (w + w')) * ∑ z, Y (Fin.cons w' z) -
        ρ₁ * (∑ w, ∑ z, X (Fin.cons w z)) * ∑ w, ∑ z, Y (Fin.cons w z)) := by
    rw [hbil, hX, hY]
    have hmid : ∑ w, ∑ w', ind (f (w + w')) * (ρ₂ * (∑ z, X (Fin.cons w z)) *
        ∑ z', Y (Fin.cons w' z')) =
        ρ₂ * ∑ w, ∑ w', (∑ z, X (Fin.cons w z)) * ind (f (w + w')) * ∑ z, Y (Fin.cons w' z) := by
      conv_rhs => rw [mul_sum]
      refine sum_congr rfl fun w _ ↦ ?_
      conv_rhs => rw [mul_sum]
      exact sum_congr rfl fun w' _ ↦ by ring
    simp only [mul_sub, sum_sub_distrib]
    rw [hmid]
    ring
  have hsq : ∀ Z : (Fin (r + 1) → Gam0 a) → ℝ, ∑ z, Z z ^ 2 = ∑ w, ∑ z, Z (Fin.cons w z) ^ 2 :=
    fun Z ↦ sum_cons _
  have h1 : |∑ w, ∑ w', ind (f (w + w')) *
      (∑ z, ∑ z', X (Fin.cons w z) * ind (g (z + z')) * Y (Fin.cons w' z') -
        ρ₂ * (∑ z, X (Fin.cons w z)) * ∑ z', Y (Fin.cons w' z'))| ≤
      e₂ * Fintype.card (Gam0 a) * (∑ z, X z ^ 2 + ∑ z, Y z ^ 2) := by
    have hpt : ∀ w w', |ind (f (w + w')) *
        (∑ z, ∑ z', X (Fin.cons w z) * ind (g (z + z')) * Y (Fin.cons w' z') -
          ρ₂ * (∑ z, X (Fin.cons w z)) * ∑ z', Y (Fin.cons w' z'))| ≤
        e₂ * (∑ z, X (Fin.cons w z) ^ 2 + ∑ z', Y (Fin.cons w' z') ^ 2) := by
      intro w w'
      rw [abs_mul, abs_of_nonneg (ind_nonneg _)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (ind_le_one _)).trans (hin w w')
    calc _ ≤ ∑ w, ∑ w', e₂ * (∑ z, X (Fin.cons w z) ^ 2 + ∑ z', Y (Fin.cons w' z') ^ 2) :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun w _ ↦
            (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun w' _ ↦ hpt w w'))
      _ = _ := by
          rw [hsq X, hsq Y]
          simp only [← mul_sum, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
          ring
  have h2 : |∑ w, ∑ w', (∑ z, X (Fin.cons w z)) * ind (f (w + w')) * ∑ z, Y (Fin.cons w' z) -
      ρ₁ * (∑ w, ∑ z, X (Fin.cons w z)) * ∑ w, ∑ z, Y (Fin.cons w z)| ≤
      e₁ * Fintype.card (Fin r → Gam0 a) * (∑ z, X z ^ 2 + ∑ z, Y z ^ 2) := by
    refine hout.trans ?_
    have hc : ∀ (Z : (Fin (r + 1) → Gam0 a) → ℝ),
        ∑ w, (∑ z, Z (Fin.cons w z)) ^ 2 ≤
          Fintype.card (Fin r → Gam0 a) * ∑ w, ∑ z, Z (Fin.cons w z) ^ 2 := by
      intro Z
      rw [mul_sum]
      refine sum_le_sum fun w _ ↦ ?_
      have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin r → Gam0 a)))
        (f := fun z ↦ Z (Fin.cons w z))
      rwa [card_univ] at this
    calc e₁ * (∑ w, (∑ z, X (Fin.cons w z)) ^ 2 + ∑ w, (∑ z, Y (Fin.cons w z)) ^ 2)
        ≤ e₁ * (Fintype.card (Fin r → Gam0 a) * ∑ w, ∑ z, X (Fin.cons w z) ^ 2 +
            Fintype.card (Fin r → Gam0 a) * ∑ w, ∑ z, Y (Fin.cons w z) ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add (hc X) (hc Y)) he₁
      _ = _ := by rw [hsq X, hsq Y]; ring
  rw [hid]
  calc _ ≤ _ + |ρ₂ * _| := abs_add_le _ _
    _ ≤ e₂ * Fintype.card (Gam0 a) * (∑ z, X z ^ 2 + ∑ z, Y z ^ 2) +
        |ρ₂| * (e₁ * Fintype.card (Fin r → Gam0 a) * (∑ z, X z ^ 2 + ∑ z, Y z ^ 2)) := by
        rw [abs_mul]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = _ := by ring

end Cons

/-! ### Dyadic densities -/

/-- The binary number `∑_l b(z_l) 2^l`. -/
def hval {r : ℕ} (z : Fin r → Gam0 a) : ℕ := ∑ l, (bent (z l)).val * 2 ^ (l : ℕ)

theorem hval_cons {r : ℕ} (w : Gam0 a) (z : Fin r → Gam0 a) :
    hval (Fin.cons w z : Fin (r + 1) → Gam0 a) = (bent w).val + 2 * hval z := by
  unfold hval
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
    pow_succ, mul_sum]
  congr 1
  exact sum_congr rfl fun _ _ ↦ by ring

theorem val_bent (w : Gam0 a) : (bent w).val = if bent w = 0 then 0 else 1 := by
  rcases zmod2_cases (bent w) with h | h <;> rw [h] <;> rfl

theorem hval_lt_iff {r : ℕ} (q : ℕ) (z : Fin (r + 1) → Gam0 a) :
    hval z < q ↔ (bent (z 0) = 0 ∧ hval (Fin.tail z) < (q + 1) / 2) ∨
      (bent (z 0) = 1 ∧ hval (Fin.tail z) < q / 2) := by
  have hz : z = Fin.cons (z 0) (Fin.tail z) := (Fin.cons_self_tail z).symm
  rw [hz, hval_cons, val_bent, Fin.cons_zero, Fin.tail_cons]
  rcases zmod2_cases (bent (z 0)) with h | h <;> simp [h] <;> omega

/-- The error of the pseudo-random sets of `Γ₀^r`. -/
noncomputable def err (a r : ℕ) : ℝ := 4 ^ r * 2 ^ a * (2 * 4 ^ a : ℝ) ^ r / (2 * 4 ^ a)

theorem err_nonneg (a r : ℕ) : 0 ≤ err a r := by unfold err; positivity

theorem err_succ (a r : ℕ) :
    2 * (err a r * (2 * 4 ^ a) + 1 * (2 ^ a / 2) * (2 * 4 ^ a : ℝ) ^ r) ≤ err a (r + 1) := by
  unfold err
  have hN : (0 : ℝ) < 2 * 4 ^ a := by positivity
  rw [div_mul_cancel₀ _ hN.ne', pow_succ (2 * 4 ^ a : ℝ), ← mul_assoc, mul_div_assoc,
    div_self hN.ne', mul_one]
  have h4 : (2 : ℝ) * 4 ^ r + 1 ≤ 4 ^ (r + 1) := by
    rw [pow_succ]; nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 4 by norm_num) (n := r)]
  have hpos : (0 : ℝ) ≤ 2 ^ a * (2 * 4 ^ a) ^ r := by positivity
  nlinarith

/-- **`{hval < q}` is `(q / 2^r, err a r)`-pseudo-random** for `q ≤ 2^r`. -/
theorem pr_lt (a : ℕ) : ∀ (r q : ℕ), q ≤ 2 ^ r →
    PR (fun z : Fin r → Gam0 a ↦ hval z < q) (q / 2 ^ r) (err a r) := by
  intro r
  induction r with
  | zero =>
    intro q hq X Y
    have hsub : ∀ z : Fin 0 → Gam0 a, z = 0 := fun z ↦ funext fun i ↦ i.elim0
    have hval0 : ∀ z : Fin 0 → Gam0 a, hval z = 0 := fun z ↦ by simp [hval]
    have hind : ind (0 < q) = (q : ℝ) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa using hq) with rfl | rfl
      · simp [ind_of_not]
      · simp [ind_of]
    simp only [hval0, hind, pow_zero, div_one]
    have e : ∑ x : Fin 0 → Gam0 a, ∑ y : Fin 0 → Gam0 a, X x * (q : ℝ) * Y y =
        (q : ℝ) * (∑ x, X x) * ∑ y, Y y :=
      calc _ = ∑ x : Fin 0 → Gam0 a, ∑ y : Fin 0 → Gam0 a, ((q : ℝ) * X x) * Y y :=
            sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
        _ = (∑ x, (q : ℝ) * X x) * ∑ y, Y y := (sum_mul_sum _ _ _ _).symm
        _ = _ := by rw [← mul_sum]
    rw [e, sub_self, abs_zero]
    exact mul_nonneg (err_nonneg a 0) (by positivity)
  | succ r ih =>
    intro q hq
    have hA := pr_cons (pr_bent (a := a) 0) (ih ((q + 1) / 2) (by rw [pow_succ] at hq; omega))
      (by positivity)
    have hB := pr_cons (pr_bent (a := a) 1) (ih (q / 2) (by rw [pow_succ] at hq; omega))
      (by positivity)
    have hor := hA.or hB (fun z h ↦ by
      have := h.1.1.symm.trans h.2.1
      exact absurd this (by decide))
    have hρ : (1 / 2 : ℝ) * (((q + 1) / 2 : ℕ) / 2 ^ r) + 1 / 2 * ((q / 2 : ℕ) / 2 ^ r) =
        q / 2 ^ (r + 1) := by
      have h : (((q + 1) / 2 : ℕ) : ℝ) + ((q / 2 : ℕ) : ℝ) = q := by
        exact_mod_cast (show (q + 1) / 2 + q / 2 = q by omega)
      rw [pow_succ, ← h]; ring
    have hle1 : |(((q + 1) / 2 : ℕ) : ℝ) / 2 ^ r| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
      exact_mod_cast (show (q + 1) / 2 ≤ 2 ^ r by rw [pow_succ] at hq; omega)
    have hle2 : |((q / 2 : ℕ) : ℝ) / 2 ^ r| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
      exact_mod_cast (show q / 2 ≤ 2 ^ r by rw [pow_succ] at hq; omega)
    rw [← hρ]
    refine (hor.congr fun z ↦ (hval_lt_iff q z).symm).mono ?_
    rw [card_gam0, Fintype.card_fun, card_gam0, Fintype.card_fin]
    push_cast
    have he := err_succ a r
    have hpos : (0 : ℝ) ≤ 2 ^ a / 2 * (2 * 4 ^ a) ^ r := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hle1 hpos, mul_le_mul_of_nonneg_right hle2 hpos]

/-! ### Counting -/

theorem card_bent_eq (c : ZMod 2) :
    ((univ.filter fun w : Gam0 a ↦ bent w = c).card : ℝ) = 4 ^ a := by
  rw [card_filter]
  push_cast
  have : ∀ w : Gam0 a, (if bent w = c then (1 : ℝ) else 0) = ind (bent w = c) := by
    intro w; unfold ind; split_ifs <;> simp
  simp_rw [this, ind_bent_eq, ← sum_div, sum_add_distrib, ← mul_sum]
  have hs : ∑ w : Gam0 a, sgn (bent w) = 0 := by
    rw [sum_gam0, sum_zmod2]
    simp only [bent, sgn_add, sgn_zero, sgn_one, one_mul, neg_one_mul, sum_neg_distrib,
      add_neg_cancel]
  rw [hs, sum_const, card_univ, card_gam0]
  ring

/-- **`{hval < q}` has exactly `q 4^(a r)` elements** for `q ≤ 2^r`. -/
theorem card_lt (a : ℕ) : ∀ (r q : ℕ), q ≤ 2 ^ r →
    ((univ.filter fun z : Fin r → Gam0 a ↦ hval z < q).card : ℝ) = q * (4 ^ a) ^ r := by
  intro r
  induction r with
  | zero =>
    intro q hq
    have hval0 : ∀ z : Fin 0 → Gam0 a, hval z = 0 := fun z ↦ by simp [hval]
    simp only [hval0, pow_zero, mul_one]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa using hq) with rfl | rfl <;> simp
  | succ r ih =>
    intro q hq
    rw [card_filter]
    push_cast
    rw [sum_cons]
    have hw : ∀ w : Gam0 a, ∑ z' : Fin r → Gam0 a,
        (if hval (Fin.cons w z' : Fin (r + 1) → Gam0 a) < q then (1 : ℝ) else 0) =
        ind (bent w = 0) * (((q + 1) / 2 : ℕ) * (4 ^ a) ^ r) +
          ind (bent w = 1) * ((q / 2 : ℕ) * (4 ^ a) ^ r) := by
      intro w
      rw [← ih ((q + 1) / 2) (by rw [pow_succ] at hq; omega),
        ← ih (q / 2) (by rw [pow_succ] at hq; omega), card_filter, card_filter]
      push_cast
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun z' _ ↦ ?_
      rw [hval_cons, val_bent]
      rcases zmod2_cases (bent w) with h | h
      · rw [ind_of h, ind_of_not (show ¬ bent w = 1 by rw [h]; decide)]
        simp only [h, ↓reduceIte, one_mul, zero_mul, add_zero, zero_add]
        split_ifs <;> first | rfl | (exfalso; omega)
      · rw [ind_of_not (show ¬ bent w = 0 by rw [h]; decide), ind_of h]
        simp only [h, show (1 : ZMod 2) ≠ 0 by decide, ↓reduceIte, one_mul, zero_mul, zero_add]
        split_ifs <;> first | rfl | (exfalso; omega)
    simp_rw [hw, sum_add_distrib, ← sum_mul]
    have h0 := card_bent_eq (a := a) 0
    have h1 := card_bent_eq (a := a) 1
    rw [card_filter] at h0 h1
    push_cast at h0 h1
    have e0 : ∑ w : Gam0 a, ind (bent w = 0) = 4 ^ a := by
      rw [← h0]; exact sum_congr rfl fun w _ ↦ by unfold ind; split_ifs <;> simp
    have e1 : ∑ w : Gam0 a, ind (bent w = 1) = 4 ^ a := by
      rw [← h1]; exact sum_congr rfl fun w _ ↦ by unfold ind; split_ifs <;> simp
    rw [e0, e1]
    have h : (((q + 1) / 2 : ℕ) : ℝ) + ((q / 2 : ℕ) : ℝ) = q := by
      exact_mod_cast (show (q + 1) / 2 + q / 2 = q by omega)
    rw [← h]; ring

/-- The translates of `{hval < q}` have as many elements. -/
theorem card_add_lt {r : ℕ} (x : Fin r → Gam0 a) (q : ℕ) :
    (univ.filter fun y : Fin r → Gam0 a ↦ hval (x + y) < q).card =
      (univ.filter fun z : Fin r → Gam0 a ↦ hval z < q).card := by
  refine card_bij (fun y _ ↦ x + y) (by simp) (fun _ _ _ _ h ↦ add_left_cancel h)
    (fun z hz ↦ ⟨z - x, by simpa using hz, by abel⟩)

end BHSV25.Hard.Cayley
