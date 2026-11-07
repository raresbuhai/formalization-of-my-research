module

public import BGHKLMM26.Hardness.Defs
public import Complexity.Foundations.Data.BitString.Block
public import Mathlib.Data.Int.CardIntervalMod

/-!
# Sums over coin blocks

Generic facts for reading numbers and points from uniform coins: sums over the bits of a
concatenation (`BGHKLMM26.Hard.sum_append`), the value of a block of `t` bits is uniform on
`[0, 2^t)` (`BGHKLMM26.Hard.sum_bitsVal`), a uniform number read modulo `M` is within `M / 2^t` of
uniform (`BGHKLMM26.Hard.abs_sum_mod_sub_le`), and `ρ`-correlated points from a uniform point
and `b`-bit thresholds (`BGHKLMM26.Hard.sum_flip_eq_corrAverage`).
-/

@[expose] public section

namespace BGHKLMM26.Hard

open Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic
  OAI.OptimalMaxCut.GaussianBellman

/-! ### Sums over bit strings -/

theorem sum_append {M : Type*} [AddCommMonoid M] (a b : ℕ) (F : List Bool → M) :
    ∑ ω : Fin (a + b) → Bool, F (List.ofFn ω) =
      ∑ ω₁ : Fin a → Bool, ∑ ω₂ : Fin b → Bool, F (List.ofFn ω₁ ++ List.ofFn ω₂) := by
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv (Fin.appendEquiv a b) _ _ fun p ↦ ?_).symm
  change _ = F (List.ofFn (Fin.append p.1 p.2))
  rw [List.ofFn_fin_append]

theorem sum_cast {M : Type*} [AddCommMonoid M] {a b : ℕ} (h : a = b) (F : List Bool → M) :
    ∑ ω : Fin a → Bool, F (List.ofFn ω) = ∑ ω : Fin b → Bool, F (List.ofFn ω) := by
  subst h; rfl

theorem bitsVal_lt (l : List Bool) : bitsVal l < 2 ^ l.length := by
  induction l with
  | nil => simp [bitsVal]
  | cons b l ih =>
    simp only [bitsVal, List.length_cons, pow_succ]
    split_ifs <;> omega

theorem bitsVal_injective {l l' : List Bool} (hl : l.length = l'.length)
    (h : bitsVal l = bitsVal l') : l = l' := by
  induction l generalizing l' with
  | nil => cases l' with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons c l ih => cases l' with
    | nil => simp at hl
    | cons c' l' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [bitsVal] at h
      have hc : c = c' := by
        cases c <;> cases c' <;> simp at h ⊢ <;> omega
      subst hc
      have : bitsVal l = bitsVal l' := by
        cases c <;> simp at h <;> omega
      rw [ih hl this]

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (m : ℕ) (φ : ℕ → M) :
    ∑ a ∈ range (2 * m), φ a = ∑ a ∈ range m, (φ (2 * a) + φ (2 * a + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- The value of `t` uniform bits is uniform on `[0, 2^t)`. -/
theorem sum_bitsVal {M : Type*} [AddCommMonoid M] (t : ℕ) (φ : ℕ → M) :
    ∑ ω : Fin t → Bool, φ (bitsVal (List.ofFn ω)) = ∑ a ∈ range (2 ^ t), φ a := by
  induction t generalizing φ with
  | zero => simp [bitsVal]
  | succ t ih =>
    rw [← (Fin.consEquiv fun _ : Fin (t + 1) ↦ Bool).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_bool]
    have ht (ω : Fin t → Bool) : bitsVal (List.ofFn ((Fin.consEquiv fun _ : Fin (t + 1) ↦ Bool)
        (true, ω))) = 1 + 2 * bitsVal (List.ofFn ω) := by
      simp [Fin.consEquiv, List.ofFn_succ, bitsVal]
    have hf (ω : Fin t → Bool) : bitsVal (List.ofFn ((Fin.consEquiv fun _ : Fin (t + 1) ↦ Bool)
        (false, ω))) = 2 * bitsVal (List.ofFn ω) := by
      simp [Fin.consEquiv, List.ofFn_succ, bitsVal]
    simp only [ht, hf]
    have h1 := ih (fun a ↦ φ (1 + 2 * a))
    have h0 := ih (fun a ↦ φ (2 * a))
    rw [h1, h0, pow_succ, mul_comm (2 ^ t) 2, sum_range_two_mul, ← sum_add_distrib]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [add_comm (φ (1 + 2 * a)), add_comm 1]

/-- Reading a block of `b` bits per coordinate gives independent uniform numbers in `[0, 2^b)`. -/
theorem sum_blocks_bitsVal {M : Type*} [AddCommMonoid M] (R b : ℕ) (φ : (Fin R → ℕ) → M) :
    ∑ ω : Fin (R * b) → Bool,
        φ (fun i ↦ bitsVal (((List.ofFn ω).drop (i * b)).take b)) =
      ∑ z : Fin R → Fin (2 ^ b), φ (fun i ↦ z i) := by
  have hblk (ω : Fin (R * b) → Bool) (i : Fin R) :
      ((List.ofFn ω).drop (i * b)).take b = List.ofFn (Cslib.BitString.block ω i) :=
    Cslib.BitString.listBlock_ofFn ω i
  simp_rw [hblk]
  rw [← (Cslib.BitString.blocksEquiv (α := Bool) (m := R) (k := b)).symm.sum_comp]
  simp only [Cslib.BitString.block_blocksEquiv_symm]
  -- the value map is a bijection `(Fin b → Bool) ≃ Fin (2^b)`
  have hinj : Function.Injective fun w : Fin b → Bool ↦
      (⟨bitsVal (List.ofFn w), by simpa using bitsVal_lt (List.ofFn w)⟩ : Fin (2 ^ b)) := by
    intro w w' h
    exact List.ofFn_injective (bitsVal_injective (by simp) (Fin.ext_iff.1 h))
  have hbij : Function.Bijective fun w : Fin b → Bool ↦
      (⟨bitsVal (List.ofFn w), by simpa using bitsVal_lt (List.ofFn w)⟩ : Fin (2 ^ b)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp⟩
  let e : (Fin b → Bool) ≃ Fin (2 ^ b) := Equiv.ofBijective _ hbij
  exact Fintype.sum_equiv (Equiv.piCongrRight fun _ ↦ e) _ _ fun w ↦ rfl

/-! ### Reading a number modulo `M` -/

theorem card_mod_eq (N M j : ℕ) (hM : 0 < M) (hj : j < M) :
    (((range N).filter fun a ↦ a % M = j).card : ℝ) ≤ N / M + 1 ∧
      (N : ℝ) / M - 1 ≤ ((range N).filter fun a ↦ a % M = j).card := by
  have hc := Nat.count_modEq_card (b := N) hM j
  rw [Nat.count_eq_card_filter_range] at hc
  have hfil : ((range N).filter fun a ↦ a ≡ j [MOD M]) = (range N).filter fun a ↦ a % M = j := by
    refine Finset.filter_congr fun a _ ↦ ?_
    rw [Nat.ModEq, Nat.mod_eq_of_lt hj]
  rw [hfil] at hc
  rw [hc]
  have hdiv : ((N / M : ℕ) : ℝ) ≤ (N : ℝ) / M := Nat.cast_div_le
  have hdiv2 : (N : ℝ) / M - 1 ≤ ((N / M : ℕ) : ℝ) := by
    have h1 : (N : ℝ) / M < ((N / M : ℕ) : ℝ) + 1 := by
      have := Nat.lt_div_mul_add (a := N) hM
      rw [div_lt_iff₀ (by exact_mod_cast hM)]
      have h2 : (N : ℝ) < ((N / M * M + M : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h2
      linarith
    linarith
  constructor
  · push_cast
    split_ifs <;> linarith
  · push_cast
    split_ifs <;> linarith

/-- **A uniform number modulo `M`**: averaging `h(a mod M)` over `a < 2^t` is within
`M / 2^t · max |h|` of the uniform average over `[0, M)`. -/
theorem abs_sum_mod_sub_le (t M : ℕ) (hM : 0 < M) (h : ℕ → ℝ) {B : ℝ}
    (hB : ∀ j < M, |h j| ≤ B) :
    |(∑ a ∈ range (2 ^ t), h (a % M)) / 2 ^ t - (∑ j ∈ range M, h j) / M| ≤ M * B / 2 ^ t := by
  have hsplit : ∑ a ∈ range (2 ^ t), h (a % M) =
      ∑ j ∈ range M, ((range (2 ^ t)).filter fun a ↦ a % M = j).card * h j := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun a ↦ a % M) (t := range M)
      (fun a _ ↦ mem_range.2 (Nat.mod_lt _ hM))]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_congr rfl fun a ha ↦ by rw [(Finset.mem_filter.1 ha).2], sum_const,
      nsmul_eq_mul]
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [hsplit, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ range M, (((range (2 ^ t)).filter fun a ↦ a % M = j).card * h j / 2 ^ t -
          h j / M)|
      ≤ ∑ j ∈ range M, |(((range (2 ^ t)).filter fun a ↦ a % M = j).card * h j / 2 ^ t -
          h j / M)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range M, B / 2 ^ t := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        have hjM := mem_range.1 hj
        obtain ⟨hc1, hc2⟩ := card_mod_eq (2 ^ t) M j hM hjM
        have hBj := hB j hjM
        rw [show ((((range (2 ^ t)).filter fun a ↦ a % M = j).card : ℝ) * h j / 2 ^ t -
            h j / M) = ((((range (2 ^ t)).filter fun a ↦ a % M = j).card : ℝ) / 2 ^ t -
              1 / M) * h j by ring, abs_mul]
        have hc : |(((range (2 ^ t)).filter fun a ↦ a % M = j).card : ℝ) / 2 ^ t - 1 / M| ≤
            1 / 2 ^ t := by
          rw [abs_le]
          have e1 : ((2 : ℝ) ^ t / M + 1) / 2 ^ t = 1 / M + 1 / 2 ^ t := by
            field_simp
          have e2 : ((2 : ℝ) ^ t / M - 1) / 2 ^ t = 1 / M - 1 / 2 ^ t := by
            field_simp
          have hc1' := div_le_div_of_nonneg_right (c := (2 : ℝ) ^ t) (by exact_mod_cast hc1)
            h2t.le
          have hc2' := div_le_div_of_nonneg_right (c := (2 : ℝ) ^ t) (by exact_mod_cast hc2)
            h2t.le
          push_cast at hc1' hc2'
          rw [e1] at hc1'
          rw [e2] at hc2'
          constructor <;> linarith
        calc |(((range (2 ^ t)).filter fun a ↦ a % M = j).card : ℝ) / 2 ^ t - 1 / M| * |h j|
            ≤ 1 / 2 ^ t * B :=
              mul_le_mul hc hBj (abs_nonneg _) (by positivity)
          _ = B / 2 ^ t := by ring
    _ = M * B / 2 ^ t := by
        rw [sum_const, card_range, nsmul_eq_mul, mul_div_assoc]

end BGHKLMM26.Hard

namespace BGHKLMM26.Hard

open Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic
  OAI.OptimalMaxCut.GaussianBellman

/-! ### Correlated points from thresholds -/

theorem sum_fin_decide_lt {M : Type*} [AddCommMonoid M] {N q : ℕ} (hq : q ≤ N) (H : Bool → M) :
    ∑ j : Fin N, H (decide ((j : ℕ) < q)) = q • H true + (N - q) • H false := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ H (decide (j < q))), ← Finset.sum_filter_add_sum_filter_not
    (range N) (fun j ↦ j < q)]
  have h1 : (range N).filter (fun j ↦ j < q) = range q := by
    ext j; simp only [mem_filter, mem_range]; omega
  have h2 : ((range N).filter fun j ↦ ¬ j < q).card = N - q := by
    have := Finset.card_filter_add_card_filter_not (s := range N) (fun j ↦ j < q)
    rw [h1, card_range, card_range] at this
    omega
  have e1 : ∑ j ∈ (range N).filter (fun j ↦ j < q), H (decide (j < q)) =
      ∑ _j ∈ (range N).filter (fun j ↦ j < q), H true :=
    sum_congr rfl fun j hj ↦ by rw [decide_eq_true (mem_filter.1 hj).2]
  have e2 : ∑ j ∈ (range N).filter (fun j ↦ ¬ j < q), H (decide (j < q)) =
      ∑ _j ∈ (range N).filter (fun j ↦ ¬ j < q), H false :=
    sum_congr rfl fun j hj ↦ by rw [decide_eq_false (mem_filter.1 hj).2]
  rw [e1, e2, sum_const, sum_const, h1, card_range, h2]

theorem flip_cons {n : ℕ} {B : ℕ} (q : ℕ) (a : Bool) (x : Fin n → Bool) (z₀ : Fin B)
    (z : Fin n → Fin B) :
    (fun i ↦ xor ((Fin.cons a x : Fin (n + 1) → Bool) i)
        (decide (((Fin.cons z₀ z : Fin (n + 1) → Fin B) i : ℕ) < q))) =
      Fin.cons (xor a (decide ((z₀ : ℕ) < q))) (fun i ↦ xor (x i) (decide ((z i : ℕ) < q))) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

/-- **`ρ`-correlated points from coins**: for `x` uniform and independent uniform `zᵢ ∈ [0, 2^b)`,
the point `y` with `yᵢ = xᵢ` flipped when `zᵢ < q` is `ρ`-correlated with `x`,
`ρ = 1 - 2q/2^b`. -/
theorem sum_flip_eq_corrAverage (b q : ℕ) (hq : q ≤ 2 ^ b) (R : ℕ)
    (F : BitCube R → BitCube R → ℝ) :
    (∑ x : Fin R → Bool, ∑ z : Fin R → Fin (2 ^ b),
        F x (fun i ↦ xor (x i) (decide ((z i : ℕ) < q)))) / (2 ^ R * (2 ^ b) ^ R) =
      corrAverage (1 - 2 * q / 2 ^ b) R F := by
  induction R with
  | zero =>
    simp only [pow_zero, mul_one, div_one, corrAverage]
    rw [Fintype.sum_unique, Fintype.sum_unique]
    congr 1 <;> funext i <;> exact Fin.elim0 i
  | succ n ih =>
    rw [corrAverage, ← ih]
    have h2b : (0 : ℝ) < 2 ^ b := by positivity
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) ↦ Bool).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply]
    have hz (a : Bool) (x : Fin n → Bool) :
        ∑ z : Fin (n + 1) → Fin (2 ^ b), F (Fin.cons a x)
            (fun i ↦ xor ((Fin.cons a x : Fin (n + 1) → Bool) i) (decide ((z i : ℕ) < q))) =
          ∑ z : Fin n → Fin (2 ^ b), ∑ z₀ : Fin (2 ^ b), F (Fin.cons a x)
            (Fin.cons (xor a (decide ((z₀ : ℕ) < q)))
              (fun i ↦ xor (x i) (decide ((z i : ℕ) < q)))) := by
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) ↦ Fin (2 ^ b)).sum_comp, Fintype.sum_prod_type,
        Finset.sum_comm]
      refine sum_congr rfl fun z _ ↦ sum_congr rfl fun z₀ _ ↦ ?_
      congr 1
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [Fin.consEquiv]
    simp only [hz]
    have hz0 (a : Bool) (x y : Fin n → Bool) :
        ∑ z₀ : Fin (2 ^ b), F (Fin.cons a x) (Fin.cons (xor a (decide ((z₀ : ℕ) < q))) y) =
          2 * 2 ^ b * ∑ c : Bool, bitPairWeight (1 - 2 * q / 2 ^ b) a c *
            F (Fin.cons a x) (Fin.cons c y) := by
      rw [sum_fin_decide_lt hq (fun f ↦ F (Fin.cons a x) (Fin.cons (xor a f) y))]
      have hq' : ((2 ^ b - q : ℕ) : ℝ) = 2 ^ b - q := by
        rw [Nat.cast_sub hq]; push_cast; ring
      simp only [nsmul_eq_mul, hq', Fintype.sum_bool]
      cases a <;> simp [bitPairWeight, sign] <;> field_simp <;> ring
    simp only [hz0]
    rw [show (2 : ℝ) ^ (n + 1) * (2 ^ b) ^ (n + 1) = 2 * 2 ^ b * (2 ^ n * (2 ^ b) ^ n) by ring,
      ← mul_div_mul_left _ (2 ^ n * (2 ^ b) ^ n : ℝ) (show (2 * 2 ^ b : ℝ) ≠ 0 by positivity)]
    congr 1
    simp only [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [Finset.sum_comm]

end BGHKLMM26.Hard
