module

public import B25.RE.Maurey

/-!
# Restricted normalized orthogonality implies restricted eigenvalues [B25, Proposition 1.10]

RNO [B25, Definition 1.9] is used here only on the directions that Maurey's method produces: the
vectors `∑ₜ ±e_{aₜ}` of `s` signed coordinates of `S` and of `Sᶜ` (`B25.TupleRNO`).

`B25.re_of_tupleRNO`: if the columns of `X` have norm `√n`, `X` satisfies this RNO at level `s`
with `ε = 1/100`, `S' ⊆ S` and `s γ_{S'}(X_S) ≥ 22500 |S'|`, then `γ_{S'}(X) ≥ 0.9 γ_{S'}(X_S)`.

The proof is the paper's. Take `z ∈ C(S')` with `z_{S'} ≠ 0`, `α = z` on `S` and `β = z` on `Sᶜ`
(`0` elsewhere), so `Xz = Xα + Xβ`, `‖β‖₁ ≤ ‖z_{S'ᶜ}‖₁ ≤ ‖α_{S'}‖₁ ≤ ‖α‖₁`, and `α ∈ C(S')`. By
Maurey's method (`B25.exists_tuple_approx`, `D = √n`) there are `α' = (‖α‖₁/s) X(∑ ±e_{aₜ})`
with coordinates in the support of `α` (so in `S`) and `‖Xα - α'‖₂ ≤ √(n/s) ‖α‖₁`, and likewise
`β'` for `β` (if `β ≠ 0`; if `β = 0`, `Xz = Xα`). RNO and `B25.abs_corr_smul_le` give
`|corr α' β'| ≤ 1/100`, so `‖α' + β'‖₂ ≥ √0.99 ‖α'‖₂` (`B25.one_sub_mul_le_dot_add`). With the
triangle inequality, `‖Xz‖₂ ≥ √0.99 ‖Xα‖₂ - 3 √(n/s) ‖α‖₁`. Then `‖Xα‖₂² ≥ n γ ‖α_{S'}‖₂²`
(`B25.reConst_cols_le`, `γ = γ_{S'}(X_S)`) and `‖α‖₁ ≤ 2 ‖α_{S'}‖₁ ≤ 2 √|S'| ‖α_{S'}‖₂` give
`‖Xz‖₂ ≥ √n ‖z_{S'}‖₂ (√(0.99 γ) - 6 √(|S'|/s))`, and `6 √(|S'|/s) ≤ √γ / 25` under the hypothesis;
`(√0.99 - 1/25)² ≥ 0.9`. Conclude with `B25.le_reConst`. If `S' = ∅` or `γ = 0` there is nothing
to prove (`B25.reConst_nonneg`).
-/

@[expose] public section

namespace B25

open Matrix

/-- **RNO on signed tuples** at level `s`: every vector `∑ₜ ±e_{aₜ}` of `s` signed coordinates of
`S` and every such vector of `Sᶜ` have images under `X` with correlation at most `ε` in absolute
value. -/
def TupleRNO {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) (s : ℕ) (ε : ℝ) :
    Prop :=
  ∀ a b : Fin s → Fin d × Bool, (∀ t, (a t).1 ∈ S) → (∀ t, (b t).1 ∉ S) →
    |corr (X *ᵥ tupleVec a) (X *ᵥ tupleVec b)| ≤ ε

namespace RN

/-- The triangle inequality in the form `‖u‖₂ ≤ ‖v‖₂ + ‖u - v‖₂`. -/
theorem l2_le_add_sub_quokka {n : ℕ} (u v : Fin n → ℝ) : l2 u ≤ l2 v + l2 (u - v) := by
  simpa using l2_add_le v (u - v)

/-- `‖u - v‖₂ = ‖v - u‖₂`. -/
theorem l2_sub_comm_quokka {n : ℕ} (u v : Fin n → ℝ) : l2 (u - v) = l2 (v - u) := by
  have h := l2_smul (-1) (u - v)
  rw [neg_one_smul, neg_sub, abs_neg, abs_one, one_mul] at h
  exact h.symm

/-- The numerical core of [B25, Proposition 1.10]: from `‖α' + β'‖₂ ≥ 0.99 ‖α'‖₂`, the triangle
inequalities, Maurey's error bounds `eA², eB² ≤ n L² / s`, `‖Xα‖₂² ≥ n γ N`, `L² ≤ 4 |S'| N` and
`s γ ≥ 22500 |S'|`, the bound `‖Xz‖₂² ≥ 0.9 n γ N`. -/
theorem numeric_core_quokka {x y p q eA eB L N k s n γ : ℝ} (hx : 0 ≤ x) (hp : 0 ≤ p)
    (heA : 0 ≤ eA) (heB : 0 ≤ eB) (hs : 0 < s) (hn : 0 ≤ n) (hN : 0 ≤ N)
    (hq1 : 99 / 100 * p ≤ q) (hq2 : q ≤ y + eA + eB) (hxp : x ≤ p + eA)
    (hA : eA ^ 2 * s ≤ n * L ^ 2) (hB : eB ^ 2 * s ≤ n * L ^ 2) (hxN : n * γ * N ≤ x ^ 2)
    (hL : L ^ 2 ≤ 4 * k * N) (hk : 22500 * k ≤ s * γ) : 9 / 10 * (n * γ * N) ≤ y ^ 2 := by
  have h1 : 5625 * (n * L ^ 2) ≤ s * x ^ 2 := by
    have h2 : n * L ^ 2 ≤ n * (4 * k * N) := mul_le_mul_of_nonneg_left hL hn
    have h3 : 22500 * k * (n * N) ≤ s * γ * (n * N) :=
      mul_le_mul_of_nonneg_right hk (mul_nonneg hn hN)
    have h4 : s * (n * γ * N) ≤ s * x ^ 2 := mul_le_mul_of_nonneg_left hxN hs.le
    nlinarith
  have herr : ∀ e : ℝ, 0 ≤ e → e ^ 2 * s ≤ n * L ^ 2 → 75 * e ≤ x := fun e he h ↦ by
    refine le_of_pow_le_pow_left₀ two_ne_zero hx ?_
    refine le_of_mul_le_mul_right ?_ hs
    nlinarith
  have hA' := herr eA heA hA
  have hB' := herr eB heB hB
  have hy : 95 / 100 * x ≤ y := by linarith
  have hy2 : (95 / 100 * x) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by positivity) hy 2
  nlinarith [sq_nonneg x]

/-- The bound of [B25, Proposition 1.10] for one vector `z` of the cone `C(S')` with
`z_{S'} ≠ 0`. -/
theorem cone_bound_quokka {n d : ℕ} {X : Matrix (Fin n) (Fin d) ℝ} {S S' : Finset (Fin d)}
    {s : ℕ} (hX : HasNormalizedColumns X) (hR : TupleRNO X S s (1 / 100)) (hS' : S' ⊆ S)
    (hs : 22500 * (S'.card : ℝ) ≤ s * reConst (cols X S) (S'.subtype (· ∈ S)))
    (hγ : 0 < reConst (cols X S) (S'.subtype (· ∈ S))) {z : Fin d → ℝ} (hz : z ∈ cone S')
    (hne : ∃ j ∈ S', z j ≠ 0) :
    9 / 10 * reConst (cols X S) (S'.subtype (· ∈ S)) ≤ reRatio X S' z := by
  set γ := reConst (cols X S) (S'.subtype (· ∈ S))
  set α : Fin d → ℝ := fun j ↦ if j ∈ S then z j else 0
  set β : Fin d → ℝ := fun j ↦ if j ∈ S then 0 else z j
  have hzαβ : z = α + β := by
    funext j
    simp only [Pi.add_apply, α, β]
    split_ifs <;> simp
  have hαS : ∀ j ∉ S, α j = 0 := fun j hj ↦ by simp [α, hj]
  have hβS : ∀ j ∈ S, β j = 0 := fun j hj ↦ by simp [β, hj]
  have hαS' : ∀ j ∈ S', α j = z j := fun j hj ↦ by simp [α, hS' hj]
  have habsα : ∀ j, |α j| ≤ |z j| := fun j ↦ by
    simp only [α]
    split_ifs <;> simp
  have habsβ : ∀ j, |β j| ≤ |z j| := fun j ↦ by
    simp only [β]
    split_ifs <;> simp
  -- `ℓ₁`-norms
  have hsplit : ∀ w : Fin d → ℝ, l1 w = ∑ j ∈ S', |w j| + ∑ j ∈ S'ᶜ, |w j| :=
    fun w ↦ (Finset.sum_add_sum_compl S' _).symm
  have hz' : ∑ j ∈ S'ᶜ, |z j| ≤ ∑ j ∈ S', |z j| := hz
  have hSα : ∑ j ∈ S', |α j| = ∑ j ∈ S', |z j| :=
    Finset.sum_congr rfl fun j hj ↦ by rw [hαS' j hj]
  have hcompα : ∑ j ∈ S'ᶜ, |α j| ≤ ∑ j ∈ S'ᶜ, |z j| := Finset.sum_le_sum fun j _ ↦ habsα j
  have hαcone' : ∑ j ∈ S'ᶜ, |α j| ≤ ∑ j ∈ S', |α j| := by
    rw [hSα]
    exact hcompα.trans hz'
  have hαcone : α ∈ cone S' := hαcone'
  have hαne : ∃ j ∈ S', α j ≠ 0 := by
    obtain ⟨j, hj, hzj⟩ := hne
    exact ⟨j, hj, by rw [hαS' j hj]; exact hzj⟩
  have hα0 : α ≠ 0 := fun h ↦ by
    obtain ⟨j, _, hj⟩ := hαne
    exact hj (by rw [h]; rfl)
  set L := l1 α with hLdef
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun j _ ↦ abs_nonneg (α j)
  have hl1β0 : 0 ≤ l1 β := Finset.sum_nonneg fun j _ ↦ abs_nonneg (β j)
  have hl1β : l1 β ≤ L := by
    rw [hsplit β, hLdef, hsplit α]
    have h0 : ∑ j ∈ S', |β j| = 0 :=
      Finset.sum_eq_zero fun j hj ↦ by rw [hβS j (hS' hj), abs_zero]
    have h1 : ∑ j ∈ S'ᶜ, |β j| ≤ ∑ j ∈ S'ᶜ, |z j| := Finset.sum_le_sum fun j _ ↦ habsβ j
    have h2 : 0 ≤ ∑ j ∈ S'ᶜ, |α j| := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
    rw [h0, hSα]
    linarith
  have hl1α : L ≤ 2 * ∑ j ∈ S', |α j| := by
    rw [hLdef, hsplit α]
    linarith
  -- the `ℓ₂`-norm on `S'`
  set N := ∑ j ∈ S', α j ^ 2
  have hNz : ∑ j ∈ S', z j ^ 2 = N := Finset.sum_congr rfl fun j hj ↦ by rw [hαS' j hj]
  have hCS : (∑ j ∈ S', |α j|) ^ 2 ≤ S'.card * N := by
    simpa [sq_abs] using Finset.sum_mul_sq_le_sq_mul_sq S' (fun _ ↦ (1 : ℝ)) fun j ↦ |α j|
  have hN : 0 < N := by
    obtain ⟨j, hj, hαj⟩ := hαne
    exact Finset.sum_pos' (fun i _ ↦ sq_nonneg _) ⟨j, hj, by positivity⟩
  have hL4 : L ^ 2 ≤ 4 * (S'.card : ℝ) * N := by
    have h1 : L ^ 2 ≤ (2 * ∑ j ∈ S', |α j|) ^ 2 := pow_le_pow_left₀ hL0 hl1α 2
    nlinarith
  -- `‖Xα‖₂² ≥ n γ N`, which also forces `n > 0`
  have hratio := reConst_cols_le X hS' hαS hαcone hαne
  have hn : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · have h0 : ((n : ℕ) : ℝ) = 0 := by exact_mod_cast h
      simp only [reRatio, h0, div_zero, zero_div] at hratio
      linarith
    · exact_mod_cast h
  have hxN : (n : ℝ) * γ * N ≤ (X *ᵥ α) ⬝ᵥ (X *ᵥ α) := by
    unfold reRatio at hratio
    rw [le_div_iff₀ hN, le_div_iff₀ hn] at hratio
    calc (n : ℝ) * γ * N = γ * N * n := by ring
      _ ≤ _ := hratio
  -- `s ≥ 1`
  have hk : (1 : ℝ) ≤ S'.card := by
    obtain ⟨j, hj, _⟩ := hne
    exact_mod_cast Finset.card_pos.2 ⟨j, hj⟩
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · exfalso
      rw [h, Nat.cast_zero, zero_mul] at hs
      linarith
    · exact h
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs1
  -- Maurey's method for `α` and `β`
  have hD : ∀ j, ∑ i, X i j ^ 2 ≤ √(n : ℝ) ^ 2 := fun j ↦ by rw [Real.sq_sqrt hn.le, hX j]
  obtain ⟨a, ha, haerr⟩ := exists_tuple_approx X hD hα0 hs1
  have haS : ∀ t, (a t).1 ∈ S := fun t ↦ by
    by_contra h
    exact ha t (hαS _ h)
  set α' := (L / s) • (X *ᵥ tupleVec a)
  have hLs : 0 ≤ L / s := div_nonneg hL0 hsR.le
  obtain ⟨β', hcorr, hberr⟩ : ∃ β' : Fin n → ℝ, |corr α' β'| ≤ 1 / 100 ∧
      (X *ᵥ β - β') ⬝ᵥ (X *ᵥ β - β') ≤ √(n : ℝ) ^ 2 * L ^ 2 / s := by
    by_cases hβ0 : β = 0
    · refine ⟨0, ?_, ?_⟩
      · simp [corr]
      · rw [hβ0, Matrix.mulVec_zero, sub_zero, dotProduct_zero]
        positivity
    · obtain ⟨b, hb, hberr⟩ := exists_tuple_approx X hD hβ0 hs1
      have hbS : ∀ t, (b t).1 ∉ S := fun t h ↦ hb t (hβS _ h)
      refine ⟨(l1 β / s) • (X *ᵥ tupleVec b), ?_, ?_⟩
      · exact (abs_corr_smul_le hLs (div_nonneg hl1β0 hsR.le) _ _).trans (hR a b haS hbS)
      · refine hberr.trans ?_
        gcongr
  -- norms
  set A := X *ᵥ α
  set B := X *ᵥ β
  have hXz : X *ᵥ z = A + B := by rw [hzαβ, Matrix.mulVec_add]
  have hmain := one_sub_mul_le_dot_add (by norm_num : (1 : ℝ) / 100 ≤ 1) hcorr
  have hp : 99 / 100 * l2 α' ≤ l2 (α' + β') := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (l2_nonneg _) ?_
    rw [← l2_sq, ← l2_sq] at hmain
    nlinarith [sq_nonneg (l2 α')]
  have hx1 : l2 A ≤ l2 α' + l2 (A - α') := l2_le_add_sub_quokka A α'
  have hq : l2 (α' + β') ≤ l2 (A + B) + l2 (A - α') + l2 (B - β') := by
    have h1 := l2_le_add_sub_quokka (α' + β') (A + B)
    have h2 : (α' + β') - (A + B) = (α' - A) + (β' - B) := by abel
    have h3 := l2_add_le (α' - A) (β' - B)
    rw [h2] at h1
    rw [l2_sub_comm_quokka α' A, l2_sub_comm_quokka β' B] at h3
    linarith
  have heA : l2 (A - α') ^ 2 * s ≤ n * L ^ 2 := by
    rw [l2_sq, ← le_div_iff₀ hsR]
    rwa [Real.sq_sqrt hn.le] at haerr
  have heB : l2 (B - β') ^ 2 * s ≤ n * L ^ 2 := by
    rw [l2_sq, ← le_div_iff₀ hsR]
    rwa [Real.sq_sqrt hn.le] at hberr
  have hfin := numeric_core_quokka (l2_nonneg A) (l2_nonneg α') (l2_nonneg _) (l2_nonneg _) hsR
    hn.le hN.le hp hq hx1 heA heB (by rw [l2_sq]; exact hxN) hL4 hs
  unfold reRatio
  rw [hNz, hXz, ← l2_sq, le_div_iff₀ hN, le_div_iff₀ hn]
  linarith

end RN

/-- **RNO implies RE** [B25, Proposition 1.10], with `ε = 1/100` and the constant `0.9` of
Theorem 1.5. -/
theorem re_of_tupleRNO {n d : ℕ} {X : Matrix (Fin n) (Fin d) ℝ} {S S' : Finset (Fin d)} {s : ℕ}
    (hX : HasNormalizedColumns X) (hR : TupleRNO X S s (1 / 100)) (hS' : S' ⊆ S)
    (hs : 22500 * (S'.card : ℝ) ≤ s * reConst (cols X S) (S'.subtype (· ∈ S))) :
    9 / 10 * reConst (cols X S) (S'.subtype (· ∈ S)) ≤ reConst X S' := by
  rcases le_or_gt (reConst (cols X S) (S'.subtype (· ∈ S))) 0 with hγ | hγ
  · linarith [reConst_nonneg X S']
  have hS'ne : S'.Nonempty := by
    rcases S'.eq_empty_or_nonempty with h | h
    · subst h
      rw [Finset.subtype_eq_empty.2 fun _ _ h ↦ Finset.notMem_empty _ h, reConst_empty] at hγ
      exact absurd hγ (lt_irrefl 0)
    · exact h
  exact le_reConst X hS'ne fun z hz hne ↦ RN.cone_bound_quokka hX hR hS' hs hγ hz hne

end B25
