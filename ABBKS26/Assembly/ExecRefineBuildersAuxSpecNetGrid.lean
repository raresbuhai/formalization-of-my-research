module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecGuard
public import Mathlib.Data.Nat.Digits.Lemmas

/-! A fuel-capped rectangular grid, enumerated by binary indices. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecNetGrid

open Common _root_.ABBKS26.Tree
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators

def digit (b j i : ℕ) : ℕ := j / b ^ i % b

def coefficient (m j i : ℕ) : ℚ := (digit (2 * m + 1) j i : ℚ) / m - 1

def point (d m : ℕ) (B : Points) (j : ℕ) : Vector :=
  (List.range d).map fun c ↦ ((List.range B.length).map fun i ↦
    coefficient m j i * (B.getD i []).getD c 0).sum

def run (d m fuel : ℕ) (B : Points) : Points :=
  (List.range (min fuel ((2 * m + 1) ^ B.length))).map (point d m B)

private theorem binary_add_of {α : Type} {enc : α ↪ List Bool} {m n : α → ℕ}
    (hm : ComputableInPolyTime m enc encNat) (hn : ComputableInPolyTime n enc encNat) :
    ComputableInPolyTime (fun a ↦ m a + n a) enc encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_add' hm.tidy hn.tidy)

theorem coefficient_polytime_of {α : Type} {enc : α ↪ List Bool}
    {m j i : α → ℕ} (hm : ComputableInPolyTime m enc encNat)
    (hj : ComputableInPolyTime j enc encNat) (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun a ↦ coefficient (m a) (j a) (i a)) enc encRat := by
  have hb := binary_add_of (binary_mul' (const 2) hm) (const 1)
  have hdiv := ComputableTidilyInPolyTime.binary_div' hj.tidy (binary_pow' hb hi).tidy
  have hmod := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.binary_mod' hdiv hb.tidy)
  exact rat_sub' (rat_div' (rat_natCast' hmod) (rat_natCast' hm)) (const 1)

theorem point_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d m j : α → ℕ} {B : α → Points}
    (hd : ComputableInPolyTime d enc encUnary) (hm : ComputableInPolyTime m enc encNat)
    (hj : ComputableInPolyTime j enc encNat) (hB : ComputableInPolyTime B enc encPoints) :
    ComputableInPolyTime (fun a ↦ point (d a) (m a) (B a) (j a)) enc encVector := by
  apply mapWithInput (range.comp hd)
  apply rat_sum'
  apply mapWithInput (range.comp ((length_list encVector).comp (hB.comp (fst _ _))))
  have hbase := (fst enc encUnary).comp (fst _ encUnary)
  exact rat_mul' (coefficient_polytime_of (hm.comp hbase) (hj.comp hbase) (snd _ _))
    (listGetDWithInput (listGetDWithInput (hB.comp hbase) (snd _ _) [])
      ((snd _ _).comp (fst _ _)) 0)

theorem run_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d m fuel : α → ℕ} {B : α → Points}
    (hd : ComputableInPolyTime d enc encUnary) (hm : ComputableInPolyTime m enc encNat)
    (hf : ComputableInPolyTime fuel enc encUnary)
    (hB : ComputableInPolyTime B enc encPoints) :
    ComputableInPolyTime (fun a ↦ run (d a) (m a) (fuel a) (B a)) enc encPoints := by
  have hb := binary_add_of (binary_mul' (const 2) hm) (const 1)
  have hpow := binary_pow' hb ((length_list encVector).comp hB)
  apply mapWithInput (range.comp (binary_min_unary' hf hpow))
  exact point_polytime_of (hd.comp (fst _ _)) (hm.comp (fst _ _))
    (unary_to_binary.comp (snd _ _)) (hB.comp (fst _ _))

theorem length_run (d m fuel : ℕ) (B : Points) :
    (run d m fuel B).length ≤ (2 * m + 1) ^ B.length := by
  simp only [run, List.length_map, List.length_range]
  exact min_le_right _ _


theorem digit_ofDigits (b : ℕ) (hb : 0 < b) (l : List ℕ)
    (hl : ∀ i ∈ l, i < b) (i : ℕ) : digit b (Nat.ofDigits b l) i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [digit]
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [digit, pow_zero, Nat.div_one, Nat.ofDigits_cons, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (hl _ List.mem_cons_self), List.getD_cons_zero]
    | succ i =>
      unfold digit
      rw [pow_succ', ← Nat.div_div_eq_div_mul,
        Nat.ofDigits_div_eq_ofDigits_tail hb _ hl, List.tail_cons]
      exact ih (fun j hj ↦ hl j (List.mem_cons_of_mem a hj)) i

/-- Every coordinate tuple occurs once enough fuel is available. Its binary index costs
only `r * log (2m+1)` bits, even when the grid itself is exponentially large. -/
theorem contains (d m fuel : ℕ) (B : Points) (hm : 0 < m)
    (hf : (2 * m + 1) ^ B.length ≤ fuel) (g : Fin B.length → Fin (2 * m + 1)) :
    ∃ j, point d m B j ∈ run d m fuel B ∧
      ∀ i : Fin B.length, coefficient m j i = (g i : ℚ) / m - 1 := by
  let l := List.ofFn fun i : Fin B.length ↦ (g i).val
  have hl : ∀ i ∈ l, i < 2 * m + 1 := by
    intro i hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    exact (g j).isLt
  let j := Nat.ofDigits (2 * m + 1) l
  have hj : j < (2 * m + 1) ^ B.length := by
    simpa only [l, List.length_ofFn] using
      Nat.ofDigits_lt_base_pow_length (by omega : 1 < 2 * m + 1) hl
  refine ⟨j, List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
  intro i
  simp [coefficient, j, digit_ofDigits _ (by omega) l hl, l,
    List.getD_eq_getElem?_getD, i.isLt]

noncomputable section

def row (d : ℕ) (B : Points) (i : Fin B.length) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun c ↦ ((B[i]).getD c.val 0 : ℝ)

theorem point_eq (d m : ℕ) (B : Points) (j : ℕ) :
    WithLp.toLp 2 (fun c : Fin d ↦ (vectorOf d (point d m B j) c : ℝ)) =
      ∑ i : Fin B.length, (coefficient m j i : ℝ) • row d B i := by
  ext c
  simp [point, vectorOf, row, List.getD_eq_getElem?_getD, c.isLt,
    SoS.Coords.sum_range_map]

/-- Rational approximations to an orthonormal basis give a covering grid with the
advertised dimension cap. This separates grid enumeration from basis normalization. -/
theorem covers {d D fuel : ℕ} (α : ℚ) (B : Points)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (b : OrthonormalBasis (Fin B.length) ℝ S)
    (hD : B.length ≤ D) (hD0 : 0 < D) (hα : 0 < α ∧ α ≤ 1 / 100)
    (happrox : ∀ i, ‖row d B i - (b i : EuclideanSpace ℝ (Fin d))‖ ≤
      (α : ℝ) / (8 * D))
    (hf : (2 * ⌈8 * (D : ℚ) / α⌉₊ + 1) ^ B.length ≤ fuel)
    (v : S) (hv : ‖v‖ = 1) :
    ∃ q ∈ run d ⌈8 * (D : ℚ) / α⌉₊ fuel B,
      ‖WithLp.toLp 2 (fun c : Fin d ↦ (vectorOf d q c : ℝ)) - v.val‖ ≤ (α : ℝ) / 4 := by
  let m := ⌈8 * (D : ℚ) / α⌉₊
  obtain ⟨hm, _, hmesh⟩ := CompleteAux.grid_size D α hD0 hα
  change 0 < m at hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
  have hαR : (0 : ℝ) < α := by exact_mod_cast hα.1
  obtain ⟨g, hg⟩ := CompleteAux.grid_cover b hm v hv.le
  obtain ⟨j, hj, hc⟩ := contains d m fuel B hm hf g
  let a : Fin B.length → ℝ := fun i ↦ (g i : ℝ) / m - 1
  have ha (i : Fin B.length) : |a i| ≤ 1 := by
    have hgi : (g i : ℝ) ≤ 2 * m := by
      exact_mod_cast (show (g i).val ≤ 2 * m by have := (g i).isLt; omega)
    have hzero : (0 : ℝ) ≤ g i := Nat.cast_nonneg _
    apply abs_le.mpr
    constructor
    · dsimp only [a]
      have hd : (0 : ℝ) ≤ (g i : ℝ) / m := div_nonneg hzero hmR.le
      linarith only [hd]
    · dsimp only [a]
      have hd : (g i : ℝ) / m ≤ 2 := (div_le_iff₀ hmR).mpr (by linarith only [hgi])
      linarith only [hd]
  have hcR (i : Fin B.length) : (coefficient m j i : ℝ) = a i := by
    have he := congrArg (Rat.castHom ℝ) (hc i)
    simpa only [Rat.coe_castHom, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_one] using he
  let center : EuclideanSpace ℝ (Fin d) := (∑ i, a i • b i : S)
  have hcenter : ‖center - v.val‖ ≤ (α : ℝ) / 8 := by
    have hb : ‖center - v.val‖ ≤ (B.length : ℝ) / m := hg
    have hBD : (B.length : ℝ) / m ≤ (D : ℝ) / m :=
      div_le_div_of_nonneg_right (by exact_mod_cast hD) hmR.le
    exact hb.trans (hBD.trans hmesh)
  let q := point d m B j
  have hdiff : WithLp.toLp 2 (fun c : Fin d ↦ (vectorOf d q c : ℝ)) - center =
      ∑ i, a i • (row d B i - (b i : EuclideanSpace ℝ (Fin d))) := by
    rw [point_eq]
    simp only [center, hcR, Submodule.coe_sum, Submodule.coe_smul,
      ← Finset.sum_sub_distrib, smul_sub]
  have hnorm : ‖WithLp.toLp 2 (fun c : Fin d ↦ (vectorOf d q c : ℝ)) - center‖ ≤
      (α : ℝ) / 8 := by
    rw [hdiff]
    calc
      _ ≤ ∑ i : Fin B.length, ‖a i •
          (row d B i - (b i : EuclideanSpace ℝ (Fin d)))‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin B.length, (α : ℝ) / (8 * D) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul (ha i) (happrox i) (norm_nonneg _) zero_le_one).trans_eq
          (one_mul _)
      _ = (B.length : ℝ) * ((α : ℝ) / (8 * D)) := by simp
      _ ≤ (D : ℝ) * ((α : ℝ) / (8 * D)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hD) (by positivity)
      _ = (α : ℝ) / 8 := by field_simp
  refine ⟨q, hj, ?_⟩
  have ht := norm_add_le
    (WithLp.toLp 2 (fun c : Fin d ↦ (vectorOf d q c : ℝ)) - center) (center - v.val)
  rw [sub_add_sub_cancel] at ht
  linarith only [ht, hnorm, hcenter]

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecNetGrid
