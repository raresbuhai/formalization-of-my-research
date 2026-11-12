module

public import BDT24.Alg.Coins
public import BDT24.Prob.Gauss
public import BDT24.Prob.Tail

/-!
# What the algorithm computes, exactly

Deterministic facts relating the algorithm's integers to the real samples.

* **Quantized samples** (`BDT24.Analysis.qz`): the input of the PCA algorithm on real points.
* **The response** (`BDT24.Analysis.floorS_eq`): `floorS t = ⌊√(2/3) t⌋`.
* **Coarsening** (`BDT24.Analysis.coarsen_quantize`): `⌊⌊2^q t⌋ / 2^(q-p)⌋ = ⌊2^p t⌋`.
* **The regression input** (`BDT24.Analysis.slrInputOf_fwd`, `BDT24.Analysis.slrInputOf_bwd`):
  on quantized samples, when no response is near a multiple of `2^(-p)`
  (`BDT24.Analysis.RespOK`, `BDT24.Analysis.respOK_of`), the regression input of the pair is
  the `p`-bit input of the regression sample `pairMap`; its length is at most `linB` on samples
  with small coordinates (`BDT24.Analysis.length_slrInputOf_le`).
* **Own samples** (`BDT24.Analysis.ownVal_eq`, `BDT24.Analysis.ownCells_eq`): the own sample read
  from the cells of Gaussian rows is their quantization, when every coordinate is at most
  `rad` and not near a multiple of `2^(-q)`: the bisection on `Φ` is within `2^(-(q+n+m+4))`
  (`BDT24.Num.abs_cellInv_sub_le`).
* **Estimates** (`BDT24.Analysis.abs_getD_le`, `BDT24.Analysis.output_length_le`): a coordinate
  of an estimate is at most `2` to the length of its encoding, which is at most the running time.
-/

@[expose] public section

namespace BDT24.Analysis

open BDT24.Alg BDT24.Prob

/-- Real points to `q` bits, one list per point: the input of the PCA algorithm. -/
noncomputable def qz (q : ℕ) {n m : ℕ} (z : Fin n → EuclideanSpace ℝ (Fin m)) : Pts :=
  List.ofFn fun i ↦ List.ofFn fun j ↦ quantize q (z i j)

theorem spcaInput_points (δ : ℚ) (p k q : ℕ) {n m : ℕ} (ω : Fin n → EuclideanSpace ℝ (Fin m)) :
    (spcaInput δ p k q ω).points = qz q ω :=
  rfl

theorem nOf_qz (q : ℕ) {n m : ℕ} (z : Fin n → EuclideanSpace ℝ (Fin m)) : nOf (qz q z) = n := by
  simp [nOf, qz]

theorem mOf_qz (q : ℕ) {n m : ℕ} (hn : 0 < n) (z : Fin n → EuclideanSpace ℝ (Fin m)) :
    mOf (qz q z) = m := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp [mOf, qz, List.ofFn_succ]

/-- `floorS t = ⌊√(2/3) t⌋`. -/
theorem floorS_eq (t : ℚ) : floorS t = ⌊√(2 / 3) * (t : ℝ)⌋ := by
  have hs : √(2 / 3 : ℝ) ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ √(2 / 3 : ℝ) := Real.sqrt_nonneg _
  have hx : ((2 * t ^ 2 / 3 : ℚ) : ℝ) = (√(2 / 3) * (t : ℝ)) ^ 2 := by
    push_cast; rw [mul_pow, hs]; ring
  unfold floorS
  split_ifs with ht
  · set N := ⌊2 * t ^ 2 / 3⌋₊
    have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht
    have hy : 0 ≤ √(2 / 3) * (t : ℝ) := mul_nonneg hs0 ht'
    have h1 : ((N : ℚ) : ℝ) ≤ ((2 * t ^ 2 / 3 : ℚ) : ℝ) := by
      exact_mod_cast Nat.floor_le (by positivity)
    have h2 : ((2 * t ^ 2 / 3 : ℚ) : ℝ) < ((N : ℚ) : ℝ) + 1 := by
      exact_mod_cast Nat.lt_floor_add_one _
    have h3 : ((Nat.sqrt N : ℕ) : ℝ) ^ 2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
    have h4 : (N : ℝ) + 1 ≤ ((Nat.sqrt N : ℕ) + 1 : ℝ) ^ 2 := by
      exact_mod_cast Nat.lt_succ_sqrt' N
    rw [hx] at h1 h2
    push_cast at h1 h2
    symm
    rw [Int.floor_eq_iff]
    push_cast
    constructor
    · nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.sqrt N)]
    · nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.sqrt N)]
  · set C := ⌈2 * t ^ 2 / 3⌉₊
    have ht' : (t : ℝ) < 0 := by exact_mod_cast not_le.1 ht
    have hy : √(2 / 3) * (t : ℝ) < 0 :=
      mul_neg_of_pos_of_neg (Real.sqrt_pos.2 (by norm_num)) ht'
    have hpos : (0 : ℚ) < 2 * t ^ 2 / 3 := by
      have : t ≠ 0 := by intro h; rw [h] at ht; exact ht le_rfl
      positivity
    have hC1 : 1 ≤ C := Nat.one_le_iff_ne_zero.2 (by
      simp only [C, ne_eq, Nat.ceil_eq_zero, not_le]; exact hpos)
    have h1 : ((2 * t ^ 2 / 3 : ℚ) : ℝ) ≤ ((C : ℚ) : ℝ) := by
      exact_mod_cast Nat.le_ceil _
    have h2 : ((C : ℚ) : ℝ) < ((2 * t ^ 2 / 3 : ℚ) : ℝ) + 1 := by
      exact_mod_cast Nat.ceil_lt_add_one hpos.le
    set s := Nat.sqrt (C - 1)
    have h3 : (s : ℝ) ^ 2 ≤ ((C - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.sqrt_le' (C - 1)
    have h4 : ((C - 1 : ℕ) : ℝ) + 1 ≤ ((s : ℝ) + 1) ^ 2 := by
      exact_mod_cast Nat.lt_succ_sqrt' (C - 1)
    have hC : ((C - 1 : ℕ) : ℝ) = (C : ℝ) - 1 := by push_cast [Nat.cast_sub hC1]; ring
    rw [hC] at h3 h4
    rw [hx] at h1 h2
    push_cast at h1 h2
    symm
    rw [Int.floor_eq_iff]
    push_cast
    constructor
    · nlinarith [Nat.cast_nonneg (α := ℝ) s]
    · nlinarith [Nat.cast_nonneg (α := ℝ) s]

/-- Coarsening a `q`-bit quantization to `p ≤ q` bits is the `p`-bit quantization. -/
theorem coarsen_quantize {p q : ℕ} (hpq : p ≤ q) (t : ℝ) :
    coarsen p q (quantize q t) = quantize p t := by
  unfold coarsen quantize
  have h2 : (2 : ℚ) ^ (q - p) = ((2 ^ (q - p) : ℕ) : ℚ) := by push_cast; ring
  have h2' : (2 : ℝ) ^ p * t = (2 : ℝ) ^ q * t / ((2 ^ (q - p) : ℕ) : ℝ) := by
    push_cast
    rw [eq_div_iff (by positivity), mul_comm _ ((2 : ℝ) ^ (q - p)), ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel hpq]
  rw [h2, h2', Int.floor_div_natCast, Int.floor_div_natCast, Int.floor_intCast]

/-- The algorithm's responses on the quantized pairs of points are the `p`-bit responses of the
regression samples. -/
def RespOK (p q : ℕ) {n d : ℕ} (z g : Fin n → EuclideanSpace ℝ (Fin (d + 1))) : Prop :=
  ∀ i, resp p q (quantize q (z i 0)) (quantize q (g i 0)) =
    quantize p (√(2 / 3) * (z i 0 + g i 0))

namespace EX

/-- Two reals within `η` of each other have the same floor when the first is not within `η` of
an integer. -/
theorem floor_eq_of_not_nearInt {a b η : ℝ} (hab : |a - b| ≤ η) (h : ¬ NearInt a η) :
    ⌊b⌋ = ⌊a⌋ := by
  have hab' := abs_le.1 hab
  rcases lt_trichotomy ⌊b⌋ ⌊a⌋ with hlt | heq | hgt
  · refine absurd ⟨⌊a⌋, ?_⟩ h
    have h1 : b < ⌊a⌋ := Int.floor_lt.1 hlt
    have h2 : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
    rw [abs_le]; constructor <;> linarith
  · exact heq
  · refine absurd ⟨⌊b⌋, ?_⟩ h
    have h1 : a < ⌊b⌋ := Int.floor_lt.1 hgt
    have h2 : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
    rw [abs_le]; constructor <;> linarith

/-- The argument of the response of two `q`-bit quantizations is within `2/2^(q-p)` of the real
one. -/
theorem abs_resp_arg_sub_le {p q : ℕ} (hpq : p ≤ q) (x y : ℝ) :
    |(2 : ℝ) ^ p * (√(2 / 3) * (x + y)) -
      √(2 / 3) * (((2 : ℚ) ^ p * (quantize q x + quantize q y) / 2 ^ q : ℚ) : ℝ)| ≤
      2 / 2 ^ (q - p) := by
  have hs0 : 0 ≤ √(2 / 3 : ℝ) := Real.sqrt_nonneg _
  have hs1 : √(2 / 3 : ℝ) ≤ 1 := Real.sqrt_le_one.2 (by norm_num)
  have hx1 : ((quantize q x : ℤ) : ℝ) ≤ 2 ^ q * x := Int.floor_le _
  have hx2 : 2 ^ q * x < ((quantize q x : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hy1 : ((quantize q y : ℤ) : ℝ) ≤ 2 ^ q * y := Int.floor_le _
  have hy2 : 2 ^ q * y < ((quantize q y : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hq : (2 : ℝ) ^ q = 2 ^ (q - p) * 2 ^ p := by rw [← pow_add, Nat.sub_add_cancel hpq]
  have hqp : (0 : ℝ) < 2 ^ (q - p) := by positivity
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  push_cast
  set a : ℝ := ((quantize q x : ℤ) : ℝ)
  set b : ℝ := ((quantize q y : ℤ) : ℝ)
  have e : (2 : ℝ) ^ p * (√(2 / 3) * (x + y)) - √(2 / 3) * (2 ^ p * (a + b) / 2 ^ q) =
      √(2 / 3) * ((2 ^ q * x - a) + (2 ^ q * y - b)) / 2 ^ (q - p) := by
    rw [hq]; field_simp; ring
  rw [e, abs_div, abs_of_pos hqp, div_le_div_iff_of_pos_right hqp, abs_mul, abs_of_nonneg hs0]
  have hab : |(2 ^ q * x - a) + (2 ^ q * y - b)| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  nlinarith [abs_nonneg ((2 ^ q * x - a) + (2 ^ q * y - b))]

end EX

/-- The responses are right unless one is near a multiple of `2^(-p)`. -/
theorem respOK_of {p q : ℕ} (hpq : p ≤ q) {n d : ℕ}
    {z g : Fin n → EuclideanSpace ℝ (Fin (d + 1))}
    (h : ∀ i, ¬ NearInt ((2 : ℝ) ^ p * (√(2 / 3) * (z i 0 + g i 0))) (2 / 2 ^ (q - p))) :
    RespOK p q z g := by
  intro i
  rw [resp, floorS_eq, quantize]
  exact EX.floor_eq_of_not_nearInt (EX.abs_resp_arg_sub_le hpq _ _) (h i)

theorem respOK_swap {p q n d : ℕ} {z g : Fin n → EuclideanSpace ℝ (Fin (d + 1))}
    (h : RespOK p q z g) : RespOK p q g z := by
  intro i
  rw [resp, add_comm, ← resp, h i, add_comm (z i 0)]

namespace EX

/-- A list over `Fin (2 * d)` is its two halves. -/
theorem ofFn_two_mul {α : Type*} {d : ℕ} (f : Fin (2 * d) → α) :
    List.ofFn f = List.ofFn (fun i : Fin d ↦ f ⟨i, by omega⟩) ++
      List.ofFn (fun i : Fin d ↦ f ⟨d + i, by omega⟩) := by
  rw [List.ofFn_congr (two_mul d) f, List.ofFn_add]
  rfl

/-- Zipping two lists of values of functions. -/
theorem zipWith_ofFn {α β γ : Type*} {n : ℕ} (f : α → β → γ) (a : Fin n → α) (b : Fin n → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn fun i ↦ f (a i) (b i) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ, ih]

/-- The design row of two quantized points: coordinates `2, …, d+1` of both, to `p` bits. -/
theorem slrRow_qz {p q d : ℕ} (hpq : p ≤ q) (x y : Fin (d + 1) → ℝ) :
    slrRow p q (List.ofFn fun i ↦ quantize q (x i)) (List.ofFn fun i ↦ quantize q (y i)) =
      List.ofFn (fun i : Fin d ↦ quantize p (x i.succ)) ++
        List.ofFn (fun i : Fin d ↦ quantize p (y i.succ)) := by
  rw [slrRow, List.ofFn_succ, List.ofFn_succ, List.tail_cons, List.tail_cons, List.map_ofFn,
    List.map_ofFn]
  congr 1 <;> (congr 1; funext i; exact coarsen_quantize hpq _)

end EX

/-- **The regression input of the pair (planted, null)** is that of the regression sample. -/
theorem slrInputOf_fwd {p q : ℕ} (hpq : p ≤ q) (k : ℕ) {n d : ℕ}
    {z g : Fin n → EuclideanSpace ℝ (Fin (d + 1))} (hR : RespOK p q z g) :
    slrInputOf k p q (qz q z) (qz q g) = slrInput k p (fun i ↦ pairMap d (z i, g i)) := by
  simp only [slrInputOf, slrInput, qz, EX.zipWith_ofFn, SLRInput.mk.injEq, true_and]
  constructor
  · congr 1
    funext j
    rw [EX.slrRow_qz hpq (z j).ofLp (g j).ofLp, EX.ofFn_two_mul]
    congr 1
    · congr 1; funext i
      simp [pairMap]
      rfl
    · congr 1; funext i
      simp [pairMap]
      rfl
  · congr 1
    funext j
    simp only [List.ofFn_succ, List.headD_cons]
    exact hR j

/-- **The regression input of the pair (null, planted)** is that of the regression sample. -/
theorem slrInputOf_bwd {p q : ℕ} (hpq : p ≤ q) (k : ℕ) {n d : ℕ}
    {z g : Fin n → EuclideanSpace ℝ (Fin (d + 1))} (hR : RespOK p q z g) :
    slrInputOf k p q (qz q g) (qz q z) = slrInput k p (fun i ↦ pairMap d (g i, z i)) :=
  slrInputOf_fwd hpq k (respOK_swap hR)

namespace EX

open Encoding in
/-- A frame doubles the length, plus one. -/
theorem length_frame (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => simp [frame]
  | cons b w ih =>
    simp only [frame, List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons,
      List.length_append] at ih ⊢
    omega

open Encoding in
/-- The encoding of a list with a first element. -/
theorem length_encList_cons {α : Type} (enc : α ↪ List Bool) (a : α) (l : List α) :
    (encList enc (a :: l)).length = 2 * (enc a).length + 1 + (encList enc l).length := by
  change (List.flatMap _ (a :: l)).length = _ + (List.flatMap _ l).length
  rw [List.flatMap_cons, List.length_append, Function.comp_apply, length_frame]

open Encoding in
/-- The encoding of a list whose elements have encodings of length at most `B`. -/
theorem length_encList_le {α : Type} (enc : α ↪ List Bool) (l : List α) (B : ℕ)
    (h : ∀ a ∈ l, (enc a).length ≤ B) : (encList enc l).length ≤ l.length * (2 * B + 1) := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    rw [length_encList_cons, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    nlinarith

open Encoding in
/-- The encoding of a pair. -/
theorem length_encPair {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) (x : α × β) :
    (encPair a b x).length = 2 * (a x.1).length + 1 + (b x.2).length := by
  change (frame _ ++ _).length = _
  rw [List.length_append, length_frame]

/-- An integer of absolute value less than `2^K` has an encoding of length at most `K + 1`. -/
theorem length_encInt_le {a : ℤ} {K : ℕ} (h : |(a : ℝ)| < 2 ^ K) :
    (Encoding.encInt a).length ≤ K + 1 := by
  have h' : a.natAbs < 2 ^ K := by
    have : ((a.natAbs : ℕ) : ℝ) < ((2 ^ K : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; exact h
    exact_mod_cast this
  change (Nat.bits a.natAbs).length + 1 ≤ K + 1
  rw [Nat.size_eq_bits_len]
  exact Nat.succ_le_succ (Nat.size_le.2 h')

/-- A `p`-bit quantization of a number of absolute value at most `R` is less than
`2^(p+R+2)`. -/
theorem abs_quantize_lt {p R : ℕ} {t : ℝ} (ht : |t| ≤ R) :
    |((quantize p t : ℤ) : ℝ)| < 2 ^ (p + R + 2) := by
  have h1 : ((quantize p t : ℤ) : ℝ) ≤ 2 ^ p * t := Int.floor_le _
  have h2 : 2 ^ p * t < (quantize p t : ℝ) + 1 := Int.lt_floor_add_one _
  have hR : (R : ℝ) + 1 ≤ 2 ^ R := by exact_mod_cast Nat.lt_two_pow_self
  have hp : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
  have ht' := abs_le.1 ht
  have e : (2 : ℝ) ^ (p + R + 2) = 2 ^ p * 2 ^ R * 4 := by rw [pow_add, pow_add]; norm_num
  have h3 : (2 : ℝ) ^ p * t ≤ 2 ^ p * R := mul_le_mul_of_nonneg_left ht'.2 (by positivity)
  have h4 : -(2 : ℝ) ^ p * R ≤ 2 ^ p * t := by nlinarith
  have h5 : (2 : ℝ) ^ p * (R + 1) ≤ 2 ^ p * 2 ^ R := mul_le_mul_of_nonneg_left hR (by positivity)
  rw [e, abs_lt]
  constructor <;> nlinarith

/-- A response of two quantized numbers of absolute value at most `R` is less than
`2^(p+R+2)`. -/
theorem abs_resp_lt {p q R : ℕ} (hpq : p ≤ q) {x y : ℝ} (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |((resp p q (quantize q x) (quantize q y) : ℤ) : ℝ)| < 2 ^ (p + R + 2) := by
  have h := abs_le.1 (abs_resp_arg_sub_le hpq x y)
  rw [resp, floorS_eq]
  set v := √(2 / 3) * (((2 : ℚ) ^ p * (quantize q x + quantize q y) / 2 ^ q : ℚ) : ℝ)
  have h1 : (⌊v⌋ : ℝ) ≤ v := Int.floor_le v
  have h2 : v < ⌊v⌋ + 1 := Int.lt_floor_add_one v
  have hqp : 2 / 2 ^ (q - p) ≤ (2 : ℝ) := div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
  have hs0 : 0 ≤ √(2 / 3 : ℝ) := Real.sqrt_nonneg _
  have hs1 : √(2 / 3 : ℝ) ≤ 1 := Real.sqrt_le_one.2 (by norm_num)
  have hw : |√(2 / 3) * (x + y)| ≤ 2 * R := by
    rw [abs_mul, abs_of_nonneg hs0]
    have : |x + y| ≤ 2 * R := (abs_add_le x y).trans (by linarith)
    nlinarith [abs_nonneg (x + y)]
  have hw' := abs_le.1 hw
  have hR : (R : ℝ) + 1 ≤ 2 ^ R := by exact_mod_cast Nat.lt_two_pow_self
  have hp : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
  have e : (2 : ℝ) ^ (p + R + 2) = 2 ^ p * 2 ^ R * 4 := by rw [pow_add, pow_add]; norm_num
  have h3 : (2 : ℝ) ^ p * (√(2 / 3) * (x + y)) ≤ 2 ^ p * (2 * R) :=
    mul_le_mul_of_nonneg_left hw'.2 (by positivity)
  have h4 : -((2 : ℝ) ^ p * (2 * R)) ≤ 2 ^ p * (√(2 / 3) * (x + y)) := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left hw'.1 (by positivity)
  have h5 : (2 : ℝ) ^ p * (R + 1) ≤ 2 ^ p * 2 ^ R := mul_le_mul_of_nonneg_left hR (by positivity)
  rw [e, abs_lt]
  constructor <;> nlinarith

end EX

/-- The regression input of two quantized samples with coordinates at most `rad` has length at
most `linB`. -/
theorem length_slrInputOf_le {p q : ℕ} (hpq : p ≤ q) (k : ℕ) {n d : ℕ}
    (z g : Fin n → EuclideanSpace ℝ (Fin (d + 1)))
    (hz : ∀ i j, |z i j| ≤ rad n (d + 1)) (hg : ∀ i j, |g i j| ≤ rad n (d + 1)) :
    (encSLRInput (slrInputOf k p q (qz q z) (qz q g))).length ≤ linB n (d + 1) k p := by
  have hD : (Encoding.encList (Encoding.encList Encoding.encInt)
      (List.zipWith (slrRow p q) (qz q z) (qz q g))).length ≤
        n * (2 * ((d + d) * (2 * (p + rad n (d + 1) + 3) + 1)) + 1) := by
    rw [qz, qz, EX.zipWith_ofFn]
    refine (EX.length_encList_le _ _ ((d + d) * (2 * (p + rad n (d + 1) + 3) + 1)) ?_).trans
      (by simp)
    intro r hr
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hr
    rw [EX.slrRow_qz hpq (z j).ofLp (g j).ofLp]
    refine (EX.length_encList_le _ _ (p + rad n (d + 1) + 3) ?_).trans (by simp)
    intro x hx
    rcases List.mem_append.1 hx with hx | hx <;> obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    · exact EX.length_encInt_le (EX.abs_quantize_lt (hz _ _))
    · exact EX.length_encInt_le (EX.abs_quantize_lt (hg _ _))
  have hY : (Encoding.encList Encoding.encInt
      (List.zipWith (fun r r' ↦ resp p q (r.headD 0) (r'.headD 0)) (qz q z) (qz q g))).length ≤
        n * (2 * (p + rad n (d + 1) + 3) + 1) := by
    rw [qz, qz, EX.zipWith_ofFn]
    refine (EX.length_encList_le _ _ (p + rad n (d + 1) + 3) ?_).trans (by simp)
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    simp only [List.ofFn_succ, List.headD_cons]
    exact EX.length_encInt_le (EX.abs_resp_lt hpq (hz _ _) (hg _ _))
  change (Encoding.encPair Encoding.encNat (Encoding.encPair Encoding.encUnary
    (Encoding.encPair (Encoding.encList (Encoding.encList Encoding.encInt))
      (Encoding.encList Encoding.encInt))) (k, p, List.zipWith (slrRow p q) (qz q z) (qz q g),
        List.zipWith (fun r r' ↦ resp p q (r.headD 0) (r'.headD 0)) (qz q z) (qz q g))).length
    ≤ _
  rw [EX.length_encPair, EX.length_encPair, EX.length_encPair]
  dsimp only
  have hu : (Encoding.encUnary p).length = p := List.length_replicate
  rw [hu]
  unfold linB
  unfold rad at hD hY
  nlinarith

namespace EX

/-- The bound of `BDT24.Num.abs_cellInv_sub_le` on the cells, `phiQ` and the `Φ` series. -/
theorem cell_bound (R E : ℕ) :
    1 / 2 ^ (E + 13 + 1) + (((R : ℝ) + 1) / 2 ^ (3 * (R + 1) ^ 2 + (E + 13)) + 2 / 2 ^ (E + 13))
      ≤ 1 / 2 ^ E := by
  have hR1 : (R : ℝ) + 1 ≤ 2 ^ (R + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := R + 1)).le
  have hle : R + 1 ≤ 3 * (R + 1) ^ 2 := by nlinarith
  have hE : (0 : ℝ) < 2 ^ E := by positivity
  have h1 : ((R : ℝ) + 1) / 2 ^ (3 * (R + 1) ^ 2 + (E + 13)) ≤ 1 / 2 ^ (E + 13) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc ((R : ℝ) + 1) * 2 ^ (E + 13) ≤ 2 ^ (R + 1) * 2 ^ (E + 13) := by gcongr
      _ = 2 ^ (R + 1 + (E + 13)) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have e1 : (1 : ℝ) / 2 ^ (E + 13 + 1) = 1 / 2 ^ E / 2 ^ 14 := by rw [div_div, ← pow_add]
  have e2 : (1 : ℝ) / 2 ^ (E + 13) = 1 / 2 ^ E / 2 ^ 13 := by rw [div_div, ← pow_add]
  have e3 : (2 : ℝ) / 2 ^ (E + 13) = 1 / 2 ^ E / 2 ^ 12 := by
    rw [div_div, ← pow_add, show E + 13 = (E + 12) + 1 by ring, pow_succ]
    field_simp
  rw [e2] at h1
  rw [e1, e3]
  have : (0 : ℝ) ≤ 1 / 2 ^ E := by positivity
  linarith

/-- The error of the bisection, `|gHat - t| ≤ 2^(-(q+n+m+4))`. -/
theorem abs_gHat_sub_le {n m q : ℕ} {t : ℝ} (ht : |t| ≤ rad n m) :
    |(gHat n m q (Gaussian.cellOf (cbits n m q) t) : ℝ) - t| ≤ 1 / 2 ^ (q + n + m + 4) := by
  obtain ⟨R, hR⟩ : ∃ R, R = rad n m := ⟨_, rfl⟩
  set E := (R + 1) ^ 2 + q + n + m + 7 with hE
  have hC : cbits n m q = E + 13 := by rw [cbits, ← hR, hE]
  have hN : phiN n m q = 3 * (R + 1) ^ 2 + (E + 13) := by rw [phiN, ← hR, hC]
  have hK : bisK n m q = (q + n + m + 5) + (R + 1) + (R + 14) := by
    rw [bisK, ← hR]; ring
  have hg : gHat n m q (Gaussian.cellOf (cbits n m q) t) =
      Num.cellInv (cbits n m q) (phiN n m q) (bisK n m q) (cbits n m q) ((R : ℚ) + 1)
        (Gaussian.cellOf (cbits n m q) t) := by rw [gHat, hR]
  rw [← hR] at ht
  have hδ : (0 : ℝ) < 1 / 2 ^ (q + n + m + 5) := by positivity
  have hB : 1 / 2 ^ (cbits n m q + 1) + (((R : ℝ) + 1) / 2 ^ (phiN n m q) + 2 / 2 ^ cbits n m q)
      ≤ 1 / 2 ^ (q + n + m + 5) * ((1 / 4) * (1 / 2) ^ ((R + 1) ^ 2)) := by
    have hrhs : 1 / 2 ^ (q + n + m + 5) * ((1 / 4) * (1 / 2 : ℝ) ^ ((R + 1) ^ 2)) =
        1 / 2 ^ E := by
      rw [one_div_pow, show E = (q + n + m + 5) + 2 + (R + 1) ^ 2 by rw [hE]; ring,
        pow_add 2 (q + n + m + 5 + 2), pow_add 2 (q + n + m + 5)]
      field_simp
      norm_num
    rw [hrhs, hC, hN]
    exact cell_bound R E
  have h := Num.abs_cellInv_sub_le (n := cbits n m q) (N := phiN n m q) (K := bisK n m q)
    (B := cbits n m q) (R := R) (g := t) (δ := 1 / 2 ^ (q + n + m + 5))
    (by rw [hC]; omega) ht
    (by rw [hN]; push_cast; linarith [(by positivity : (0 : ℝ) ≤ ((E + 13 : ℕ) : ℝ))]) hδ hB
  have hK' : 2 * ((R : ℝ) + 1) / 2 ^ bisK n m q ≤ 1 / 2 ^ (q + n + m + 5) := by
    rw [hK, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    generalize q + n + m + 5 = a
    have hR1 : (R : ℝ) + 1 ≤ 2 ^ (R + 1) := by
      exact_mod_cast (Nat.lt_two_pow_self (n := R + 1)).le
    have h14 : (2 : ℝ) ≤ 2 ^ (R + 14) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_add, pow_add]
    have h0 : (0 : ℝ) < 2 ^ a := by positivity
    have h1 : (0 : ℝ) ≤ (R : ℝ) + 1 := by positivity
    calc 2 * ((R : ℝ) + 1) * 2 ^ a = 2 ^ a * ((R + 1) * 2) := by ring
      _ ≤ 2 ^ a * (2 ^ (R + 1) * 2 ^ (R + 14)) := by gcongr
      _ = _ := by ring
  have e : (1 : ℝ) / 2 ^ (q + n + m + 4) =
      1 / 2 ^ (q + n + m + 5) + 1 / 2 ^ (q + n + m + 5) := by
    rw [pow_succ]; field_simp; ring
  rw [hg, e]
  exact h.trans (by linarith)

end EX

/-- **An own coordinate** is the quantization of the Gaussian of its cell, when that is at most
`rad` and not near a multiple of `2^(-q)`. -/
theorem ownVal_eq {n m q : ℕ} {t : ℝ} (ht : |t| ≤ rad n m)
    (hfar : ¬ NearInt ((2 : ℝ) ^ q * t) (1 / 2 ^ (n + m + 4))) :
    ownVal n m q (Gaussian.cellOf (cbits n m q) t) = quantize q t := by
  have h := EX.abs_gHat_sub_le (q := q) ht
  rw [ownVal, quantize, ← Rat.floor_cast (α := ℝ)]
  push_cast
  refine EX.floor_eq_of_not_nearInt ?_ hfar
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity), abs_sub_comm]
  calc (2 : ℝ) ^ q * |(gHat n m q (Gaussian.cellOf (cbits n m q) t) : ℝ) - t| ≤
      2 ^ q * (1 / 2 ^ (q + n + m + 4)) := by gcongr
    _ = 1 / 2 ^ (n + m + 4) := by
      rw [show q + n + m + 4 = q + (n + m + 4) by ring, pow_add]; field_simp

/-- **The own sample** is the quantization of the Gaussian rows. -/
theorem ownCells_eq {n m q : ℕ} (g : Fin n → EuclideanSpace ℝ (Fin m))
    (h : ∀ i j, |g i j| ≤ rad n m ∧ ¬ NearInt ((2 : ℝ) ^ q * g i j) (1 / 2 ^ (n + m + 4))) :
    ownCells n m q g = qz q g := by
  simp only [ownCells, qz]
  congr 1; funext i; congr 1; funext j
  exact ownVal_eq (h i j).1 (h i j).2

namespace EX

/-- An integer is less than `2` to the length of its encoding. -/
theorem natAbs_lt_two_pow_encInt (a : ℤ) : a.natAbs < 2 ^ (Encoding.encInt a).length := by
  have h := Nat.lt_size_self a.natAbs
  rw [← Nat.size_eq_bits_len] at h
  refine h.trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
  change _ ≤ (Nat.bits a.natAbs).length + 1
  omega

/-- A rational is at most `2` to the length of its encoding. -/
theorem abs_le_two_pow_encRat (x : ℚ) : |(x : ℝ)| ≤ 2 ^ (Encoding.encRat x).length := by
  have h1 : (x.num.natAbs : ℝ) < 2 ^ (Encoding.encInt x.num).length := by
    exact_mod_cast natAbs_lt_two_pow_encInt x.num
  have h2 : (Encoding.encInt x.num).length ≤ (Encoding.encRat x).length := by
    change _ ≤ (Encoding.encPair Encoding.encInt Encoding.encNat (x.num, x.den)).length
    rw [length_encPair]
    dsimp only
    omega
  have h3 : |(x : ℝ)| ≤ x.num.natAbs := by
    rw [Nat.cast_natAbs, Int.cast_abs, Rat.cast_def, abs_div, Nat.abs_cast]
    exact div_le_self (abs_nonneg _) (by exact_mod_cast x.den_pos)
  calc |(x : ℝ)| ≤ x.num.natAbs := h3
    _ ≤ 2 ^ (Encoding.encInt x.num).length := h1.le
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) h2

end EX

/-- A coordinate of an estimate is at most `2` to the length of its encoding. -/
theorem abs_getD_le (est : Estimate) (j : ℕ) :
    |((est.getD j 0 : ℚ) : ℝ)| ≤ 2 ^ (encEstimate est).length := by
  induction est generalizing j with
  | nil => simp
  | cons a l ih =>
    have hl : (encEstimate (a :: l)).length =
        2 * (Encoding.encRat a).length + 1 + (encEstimate l).length :=
      EX.length_encList_cons _ _ _
    rw [hl]
    cases j with
    | zero =>
      simp only [List.getD_cons_zero]
      exact (EX.abs_le_two_pow_encRat a).trans (pow_le_pow_right₀ (by norm_num) (by omega))
    | succ j =>
      simp only [List.getD_cons_succ]
      exact (ih j).trans (pow_le_pow_right₀ (by norm_num) (by omega))

/-- The output of a machine is no longer than its running time. -/
theorem output_length_le {A : SLRInput × List Bool → Estimate} {e : ℕ}
    (h : RunsInTime encSLRInput encEstimate A (slrTime e)) :
    ∃ cA : ℕ, ∀ I r, (encEstimate (A (I, r))).length ≤
      cA * (slrTime e I + (Encoding.encPair encSLRInput Encoding.encBits (I, r)).length + 1) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun I r ↦ hc.length_le (I, r)⟩

end BDT24.Analysis
