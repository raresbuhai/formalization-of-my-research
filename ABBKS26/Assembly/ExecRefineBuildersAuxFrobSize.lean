module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobGuard

/-! Explicit rational bit bounds for every edge of the threshold scan. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FrobSize

open Common _root_.ABBKS26.Tree
open Turing.MultiTapeTM

/-- Magnitude and denominator bounds suffice for binary encoding, without a dyadic input. -/
structure RatBound (b : ℕ) (q : ℚ) : Prop where
  magnitude : |q| ≤ 2 ^ b
  denominator : q.den ≤ 2 ^ b

theorem RatBound.mono {a b : ℕ} {q : ℚ} (h : RatBound a q) (hab : a ≤ b) :
    RatBound b q :=
  ⟨h.magnitude.trans (pow_le_pow_right₀ (by norm_num) hab),
    h.denominator.trans (Nat.pow_le_pow_right (by norm_num) hab)⟩

theorem RatBound.zero (b : ℕ) : RatBound b 0 := by
  exact ⟨by simp, by simpa using Nat.one_le_two_pow⟩

theorem RatBound.one : RatBound 0 1 := by constructor <;> norm_num

theorem RatBound.neg {b : ℕ} {q : ℚ} (h : RatBound b q) : RatBound b (-q) := by
  exact ⟨by simpa only [abs_neg] using h.magnitude,
    by simpa only [Rat.den_neg_eq_den] using h.denominator⟩

theorem RatBound.mul {a b : ℕ} {q r : ℚ} (hq : RatBound a q) (hr : RatBound b r) :
    RatBound (a + b) (q * r) := by
  constructor
  · rw [abs_mul, pow_add]
    exact mul_le_mul hq.magnitude hr.magnitude (abs_nonneg _) (by positivity)
  · apply (Nat.le_of_dvd (by positivity) (Rat.mul_den_dvd q r)).trans
    simpa only [pow_add] using Nat.mul_le_mul hq.denominator hr.denominator

theorem RatBound.add {a b : ℕ} {q r : ℚ} (hq : RatBound a q) (hr : RatBound b r) :
    RatBound (a + b + 1) (q + r) := by
  have ha : (1 : ℚ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
  have hb : (1 : ℚ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  constructor
  · apply (abs_add_le q r).trans
    calc
      _ ≤ 2 ^ a + 2 ^ b := add_le_add hq.magnitude hr.magnitude
      _ ≤ 2 ^ a * 2 ^ b + 2 ^ a * 2 ^ b :=
        add_le_add (le_mul_of_one_le_right (by positivity) hb)
          (le_mul_of_one_le_left (by positivity) ha)
      _ = _ := by rw [pow_succ, pow_add]; ring
  · apply (Nat.le_of_dvd (by positivity) (Rat.add_den_dvd q r)).trans
    exact (Nat.mul_le_mul hq.denominator hr.denominator).trans
      (by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega))

theorem RatBound.sub {a b : ℕ} {q r : ℚ} (hq : RatBound a q) (hr : RatBound b r) :
    RatBound (a + b + 1) (q - r) := by
  simpa only [sub_eq_add_neg] using hq.add hr.neg

theorem RatBound.half {b : ℕ} {q : ℚ} (hq : RatBound b q) :
    RatBound (b + 1) (q / 2) := by
  have hh : RatBound 1 (1 / 2) := by constructor <;> norm_num
  simpa only [div_eq_mul_inv, one_mul] using hq.mul hh

theorem RatBound.sum {xs : List ℚ} {b : ℕ} (h : ∀ q ∈ xs, RatBound b q) :
    RatBound (xs.length * (b + 1)) xs.sum := by
  induction xs with
  | nil => simpa using RatBound.zero 0
  | cons q xs ih =>
    have hx := ih (fun r hr ↦ h r (List.mem_cons_of_mem _ hr))
    have hs := (h q List.mem_cons_self).add hx
    rw [List.sum_cons]
    apply hs.mono
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem RatBound.bits {b : ℕ} {q : ℚ} (h : RatBound b q) :
    (Encoding.encRat q).length ≤ 6 * b + 6 := by
  have hn : q.num.natAbs ≤ 2 ^ (2 * b) := by
    have he : (q.num.natAbs : ℚ) = |q| * q.den := by
      rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.mul_den_eq_num, abs_mul,
        abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)]
    have hd : (q.den : ℚ) ≤ 2 ^ b := by exact_mod_cast h.denominator
    have hb : (q.num.natAbs : ℚ) ≤ 2 ^ (2 * b) := by
      rw [he, two_mul, pow_add]
      exact mul_le_mul h.magnitude hd (by positivity) (by positivity)
    exact_mod_cast hb
  have hn' : q.num.natAbs < 2 ^ (2 * b + 1) :=
    hn.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hd' : q.den < 2 ^ (2 * b + 1) :=
    h.denominator.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  change (encPair encIntBin encNat (q.num, q.den)).length ≤ _
  rw [length_encPair, length_encIntBin]
  have hnum := Nat.size_le.mpr hn'
  have hden := length_encNat_le_of_lt_two_pow hd'
  simp only at hnum hden ⊢
  omega

/-- This applies to each coefficient of a clamped dyadic replacement. -/
theorem of_small {p b : ℕ} {q : ℚ} (h : SoS.PolyTime.Small p b q) :
    RatBound (b + p + 1) q := by
  exact ⟨h.1.trans (pow_le_pow_right₀ (by norm_num) (by omega)), h.lt.2.le⟩

theorem of_encoding {b : ℕ} {q : ℚ} (hq : (Encoding.encRat q).length ≤ b) :
    RatBound b q := by
  change (encPair encIntBin encNat (q.num, q.den)).length ≤ b at hq
  simp only [length_encPair, length_encIntBin, encNat_apply, Nat.size_eq_bits_len] at hq
  have hn : q.num.natAbs < 2 ^ b := Nat.size_le.mp (by omega)
  have hd : q.den < 2 ^ b := Nat.size_le.mp (by omega)
  constructor
  · have he : (q.num.natAbs : ℚ) = |q| * q.den := by
      rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.mul_den_eq_num, abs_mul,
        abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)]
    have hd1 : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
    have hm : |q| ≤ (q.num.natAbs : ℚ) := by
      rw [he]
      exact le_mul_of_one_le_right (abs_nonneg _) hd1
    exact hm.trans (by exact_mod_cast hn.le)
  · exact hd.le

theorem getD_bound {xs : Vector} {b : ℕ} (h : ∀ q ∈ xs, RatBound b q) (i : ℕ) :
    RatBound b (xs.getD i 0) := by
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega : xs.length ≤ i)]
    exact RatBound.zero _

/-- Even defaulted coordinates of malformed points obey the original sample's bit bound. -/
theorem point_bound (pts : Points) (i j : ℕ) :
    RatBound (encPoints pts).length ((pts.getD i []).getD j 0) := by
  by_cases hi : i < pts.length
  · rw [List.getD_eq_getElem _ _ hi]
    apply getD_bound
    intro q hq
    apply of_encoding
    exact (length_le_encList_of_mem Encoding.encRat hq).trans
      (length_le_encList_of_mem encVector (List.getElem_mem hi))
  · rw [List.getD_eq_default _ _ (by omega : pts.length ≤ i)]
    exact RatBound.zero _

def evalBound (d a x : ℕ) : ℕ :=
  d * (d * (x + a + x + 1) + 1) + d * (a + x + 1) + a + 2

theorem evalBound_le (d a x z : ℕ) (hz : 2 ≤ z) (hd : d ≤ z)
    (ha : a ≤ z ^ 4) (hx : x ≤ z ^ 4) : evalBound d a x ≤ 20 * z ^ 6 := by
  have hZ : 1 ≤ z ^ 4 := one_le_pow₀ (by omega)
  have hmono : evalBound d a x ≤ evalBound d (z ^ 4) (z ^ 4) := by
    unfold evalBound
    gcongr
  have hpoly : evalBound d (z ^ 4) (z ^ 4) ≤ 4 * (d + 1) ^ 2 * z ^ 4 := by
    unfold evalBound
    nlinarith only [hZ, Nat.mul_le_mul_left d hZ, Nat.mul_le_mul_left (d * d) hZ]
  have hs : (d + 1) ^ 2 ≤ (2 * z) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  calc
    _ ≤ 4 * (d + 1) ^ 2 * z ^ 4 := hmono.trans hpoly
    _ ≤ 4 * (2 * z) ^ 2 * z ^ 4 := by gcongr
    _ = 16 * z ^ 6 := by ring
    _ ≤ _ := by omega

/-- The quadratic evaluation has a fixed polynomial bit bound in dimension and entry bits.
This includes every affine coefficient, although the rounded program sets them to zero. -/
theorem eval_bound (d : ℕ) (q : StatisticL) (x : Vector) (a b : ℕ)
    (hA : ∀ i < d, ∀ j < d, RatBound a ((q.1.getD i []).getD j 0))
    (hb : ∀ i < d, RatBound a (q.2.1.getD i 0)) (hc : RatBound a q.2.2)
    (hx : ∀ i < d, RatBound b (x.getD i 0)) :
    RatBound (evalBound d a b) (evalL d q x) := by
  have hrow (i : ℕ) (hi : i < d) :
      RatBound (d * (b + a + b + 1))
        (((List.range d).map fun j ↦
          x.getD i 0 * (q.1.getD i []).getD j 0 * x.getD j 0).sum) := by
    have hterms : ∀ z ∈ (List.range d).map (fun j ↦
        x.getD i 0 * (q.1.getD i []).getD j 0 * x.getD j 0),
        RatBound (b + a + b) z := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
      exact ((hx i hi).mul (hA i hi j (List.mem_range.mp hj))).mul
        (hx j (List.mem_range.mp hj))
    simpa only [List.length_map, List.length_range] using RatBound.sum hterms
  have hquad : RatBound (d * (d * (b + a + b + 1) + 1))
      (((List.range d).map fun i ↦ ((List.range d).map fun j ↦
        x.getD i 0 * (q.1.getD i []).getD j 0 * x.getD j 0).sum).sum) := by
    apply (RatBound.sum (b := d * (b + a + b + 1)) ?_).mono (by simp)
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    exact hrow i (List.mem_range.mp hi)
  have hlin : RatBound (d * (a + b + 1))
      (((List.range d).map fun i ↦ q.2.1.getD i 0 * x.getD i 0).sum) := by
    apply (RatBound.sum (b := a + b) ?_).mono (by simp)
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    exact (hb i (List.mem_range.mp hi)).mul (hx i (List.mem_range.mp hi))
  exact ((hquad.add hlin).add hc).mono (by unfold evalBound; omega)

theorem cells_bound {xs : List ℚ} {b : ℕ} (h : ∀ q ∈ xs, RatBound b q) :
    ∀ t ∈ Thresholds.cells xs, RatBound (2 * b + 2) t := by
  intro t ht
  simp only [Thresholds.cells, List.mem_append, List.mem_singleton, List.mem_map,
    List.mem_flatMap] at ht
  rcases ht with (((rfl | ht) | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩) | ⟨q, hq, r, hr, rfl⟩
  · exact RatBound.zero _
  · exact (h t ht).mono (by omega)
  · exact ((h q hq).sub RatBound.one).mono (by omega)
  · exact ((h q hq).add RatBound.one).mono (by omega)
  · exact ((h q hq).add (h r hr)).half |>.mono (by omega)

/-- Every threshold is bounded, including both unbounded cells and all pairwise midpoints. -/
theorem scan_bound (d : ℕ) (pts : Points) (N : List ℕ) (q : StatisticL) (W : ℚ)
    (v b : ℕ) (hv : ∀ i ∈ N, RatBound v (evalL d q (pts.getD i [])))
    (hW : RatBound b W) :
    ∀ t ∈ Thresholds.scan d pts N q W, RatBound (2 * (v + b + 1) + 2) t := by
  apply cells_bound
  intro t ht
  obtain ⟨i, hi, ht⟩ := List.mem_flatMap.mp ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact (hv i hi).mono (by omega)
  · exact (hv i hi).sub hW
  · exact (hv i hi).add hW

/-- The entire raw scan fits one explicit bound, with all edge metadata and endpoints.
Only the evaluation bound is needed; no chosen threshold or verification predicate occurs. -/
theorem raw_bits (d : ℕ) (pts : Points) (h : ℕ) (N : List ℕ) (q : StatisticL)
    (W : ℚ) (v b Q : ℕ) (hq : (encStatistic q).length ≤ Q)
    (hv : ∀ i ∈ N, RatBound v (evalL d q (pts.getD i []))) (hW : RatBound b W) :
    ∀ e ∈ Thresholds.rawL d pts h N q W,
      (encEdge e).length ≤
        2 * (encNat h).length + 2 * (encIndices N).length + 2 * Q +
          2 * (encNat 1).length + 5 * (6 * (2 * (v + b + 1) + 2 + b + 1) + 6) + 6 := by
  intro e he
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
  have ht' := scan_bound d pts N q W v b hv hW t ht
  have htb := (ht'.mono (show 2 * (v + b + 1) + 2 ≤
    2 * (v + b + 1) + 2 + b + 1 by omega)).bits
  have hlo := (ht'.sub hW).bits
  have hhi := (ht'.add hW).bits
  change (encPair encNat (encPair encIndices (encPair encStatistic
    (encPair encNat (encPair Encoding.encRat (encPair Encoding.encRat Encoding.encRat)))))
      (Thresholds.edge h N q W t)).length ≤ _
  simp only [encStatistic, length_encPair] at hq
  simp only [length_encPair, Thresholds.edge]
  omega


end ABBKS26.Assembly.Exec.RefineSynth.FrobSize
