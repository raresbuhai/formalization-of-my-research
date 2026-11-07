module

public import BKS23.Assembly
public import BKS23.Algorithm1

/-!
# The size condition of Theorem 5.6 (1)

Consequences of `32 max{n^(2/3) p^(1/3) / (1 - p)^(2/3), √n log n} ≤ k ≤ n` for the parameter
`q = max(p, 1/√n)` at which the random graph is analysed (`BKS23.Size1.q_facts`), and for the
cleanup threshold `Δ = ⌊k² / (n (log₂ n + 1))⌋ + 1` (`BKS23.Size1.delta1_facts`,
`BKS23.Size1.nb_facts`).
-/

@[expose] public section

namespace BKS23.Size1

open Real

/-! ### Cubes and squares of the size condition -/

theorem cube_le {n k : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1)
    (h : 32 * ((n : ℝ) ^ (2 / 3 : ℝ) * p ^ (1 / 3 : ℝ) / (1 - p) ^ (2 / 3 : ℝ)) ≤ k) :
    32768 * (n : ℝ) ^ 2 * p ≤ (k : ℝ) ^ 3 * (1 - p) ^ 2 := by
  have hq : 0 < 1 - p := by linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set a := (n : ℝ) ^ (2 / 3 : ℝ) * p ^ (1 / 3 : ℝ) / (1 - p) ^ (2 / 3 : ℝ) with ha
  have ha0 : 0 ≤ a := by positivity
  have h3 : (32 * a) ^ 3 ≤ (k : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) h 3
  have hcube : ∀ x : ℝ, 0 ≤ x → ∀ r : ℝ, (x ^ r) ^ (3 : ℕ) = x ^ (r * 3) := fun x hx r ↦ by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  have ha3 : a ^ 3 = (n : ℝ) ^ 2 * p / (1 - p) ^ 2 := by
    rw [ha, div_pow, mul_pow, hcube _ hn, hcube _ hp, hcube _ hq.le]
    norm_num
  have : (32 * a) ^ 3 = 32768 * ((n : ℝ) ^ 2 * p / (1 - p) ^ 2) := by
    rw [mul_pow, ha3]; norm_num
  rw [this] at h3
  have hq2 : 0 < (1 - p) ^ 2 := by positivity
  rw [mul_div_assoc', div_le_iff₀ hq2] at h3
  linarith

theorem sqrt_facts {n k : ℕ} (hn : 1 ≤ n) (hlog : 1 ≤ Real.log n)
    (h : 32 * (√(n : ℝ) * Real.log n) ≤ k) :
    32768 * ((n : ℝ) * √n) ≤ (k : ℝ) ^ 3 ∧ 1024 * n * Real.log n ^ 2 ≤ (k : ℝ) ^ 2 ∧
      √(n : ℝ) ≤ k ∧ (n : ℝ) ≤ (k : ℝ) ^ 2 := by
  set s := √(n : ℝ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hs1 : 1 ≤ s := by
    rw [hs, Real.one_le_sqrt]; exact_mod_cast hn
  have hL := hlog
  have hsk : s ≤ k := by nlinarith
  have hk0 : (0 : ℝ) ≤ k := hs0.trans hsk
  refine ⟨?_, ?_, hsk, ?_⟩
  · have h1 : (32 * s) ^ 3 ≤ (k : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (le_trans (by nlinarith) h) 3
    have hs3 : s ^ 3 = n * s := by rw [pow_succ, hss]
    have : (32 * s) ^ 3 = 32768 * (n * s) := by rw [mul_pow, hs3]; norm_num
    linarith
  · have h1 : (32 * (s * Real.log n)) ^ 2 ≤ (k : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h 2
    have : (32 * (s * Real.log n)) ^ 2 = 1024 * n * Real.log n ^ 2 := by
      rw [mul_pow, mul_pow, hss]; ring
    linarith
  · have h1 : s ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ hs0 hsk 2
    linarith

/-! ### The parameter `q = max(p, 1/√n)` -/

/-- **The parameter `q`.** For `n ≥ 4`, `0 ≤ p < 1`, `k ≤ n` with `32768 n² p ≤ k³ (1 - p)²`,
`32768 n √n ≤ k³` and `√n ≤ k`, the parameter `q = max(p, 1/√n)` has `1/√n ≤ q < 1`,
`1/(1 - q) ≤ √n`, `4608 n² q ≤ (1 - q)² k³`, `√n / 2 ≤ (1 - q) k` and `1 ≤ 18 n q (1 - q)`. -/
theorem q_facts {n k : ℕ} {p : ℝ} (hn : 4 ≤ n) (hp : 0 ≤ p) (hp1 : p < 1) (hkn : k ≤ n)
    (hc : 32768 * (n : ℝ) ^ 2 * p ≤ (k : ℝ) ^ 3 * (1 - p) ^ 2)
    (hs : 32768 * ((n : ℝ) * √n) ≤ (k : ℝ) ^ 3) (hk : √(n : ℝ) ≤ k) :
    1 / √(n : ℝ) ≤ max p (1 / √n) ∧ max p (1 / √n) < 1 ∧
      1 / (1 - max p (1 / √n)) ≤ √(n : ℝ) ∧
      4608 * (n : ℝ) ^ 2 * max p (1 / √n) ≤ (1 - max p (1 / √n)) ^ 2 * (k : ℝ) ^ 3 ∧
      √(n : ℝ) / 2 ≤ (1 - max p (1 / √n)) * k ∧
      1 ≤ 18 * n * (max p (1 / √n) * (1 - max p (1 / √n))) := by
  set s := √(n : ℝ) with hsdef
  set q := max p (1 / s) with hqdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hs2 : 2 ≤ s := by nlinarith
  have hsp : 0 < s := by linarith
  have hinv : 1 / s ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hsp (by norm_num)]; linarith
  have hinv0 : 0 < 1 / s := by positivity
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hk0 : (0 : ℝ) ≤ k := hs0.trans hk
  have hq1 : q < 1 := max_lt hp1 (by linarith)
  have hq0 : 1 / s ≤ q := le_max_right _ _
  have hqp : 0 < q := lt_of_lt_of_le hinv0 hq0
  have hn0 : (0 : ℝ) < n := by linarith
  -- For `q > 1/2`, `q = p` and `1 - p ≥ 128 / √n`.
  have hbig : 1 / 2 < q → q = p ∧ 128 ≤ (1 - p) * s ∧ 128 * s ≤ (1 - p) * k := by
    intro hq
    have hqp' : q = p := by
      rcases le_total p (1 / s) with h | h
      · exfalso; rw [hqdef, max_eq_right h] at hq; linarith
      · rw [hqdef, max_eq_left h]
    have hp2 : 1 / 2 < p := hqp' ▸ hq
    have h16 : 16384 * (n : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 * (1 - p) ^ 2 := by nlinarith
    -- `(1 - p)² k² ≥ 16384 n² / k ≥ 16384 n`.
    have hk3 : (k : ℝ) ^ 3 ≤ n * (k : ℝ) ^ 2 := by
      rw [pow_succ]; nlinarith [sq_nonneg (k : ℝ)]
    have hkpos : (0 : ℝ) < k := lt_of_lt_of_le hsp hk
    have h1 : 16384 * (n : ℝ) ≤ ((1 - p) * k) ^ 2 := by
      have : 16384 * (n : ℝ) ^ 2 ≤ n * (k : ℝ) ^ 2 * (1 - p) ^ 2 :=
        h16.trans (mul_le_mul_of_nonneg_right hk3 (sq_nonneg _))
      have : 16384 * (n : ℝ) * n ≤ ((1 - p) * k) ^ 2 * n := by nlinarith
      exact le_of_mul_le_mul_right this hn0
    have h2 : 16384 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 * (1 - p) ^ 2 := by
      refine h16.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
      exact pow_le_pow_left₀ hk0 hkn' 3
    have h3 : 16384 ≤ ((1 - p) * s) ^ 2 := by
      have : 16384 * (n : ℝ) ^ 2 ≤ ((1 - p) * s) ^ 2 * (n : ℝ) ^ 2 := by
        rw [mul_pow, hss]; nlinarith
      exact le_of_mul_le_mul_right this (by positivity)
    have hps : 0 ≤ (1 - p) * s := by have : 0 < 1 - p := by linarith
                                     positivity
    have hpk : 0 ≤ (1 - p) * k := by have : 0 < 1 - p := by linarith
                                     positivity
    refine ⟨hqp', ?_, ?_⟩
    · nlinarith
    · have : (128 * s) ^ 2 ≤ ((1 - p) * k) ^ 2 := by rw [mul_pow, hss]; linarith
      exact (pow_le_pow_iff_left₀ (by positivity) hpk (by norm_num)).1 this
  -- `1 - q ≥ 1/√n`.
  have hcq : 1 / s ≤ 1 - q := by
    rcases le_or_gt q (1 / 2) with h | h
    · linarith
    · obtain ⟨hqp', h1, -⟩ := hbig h
      rw [hqp', div_le_iff₀ hsp]; linarith
  have hq10 : 0 < 1 - q := lt_of_lt_of_le hinv0 hcq
  refine ⟨hq0, hq1, ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hq10]
    have := mul_le_mul_of_nonneg_left hcq hs0
    rw [mul_one_div_cancel hsp.ne'] at this
    linarith
  · rcases le_total p (1 / s) with h | h
    · -- `q = 1/√n`: `(1 - q)² k³ ≥ k³ / 4 ≥ 8192 n √n = 8192 n² q`.
      have hq : q = 1 / s := by rw [hqdef, max_eq_right h]
      have h1 : 1 / 4 ≤ (1 - q) ^ 2 := by nlinarith
      have h2 : (n : ℝ) ^ 2 * q = n * s := by
        rw [hq, ← hss]; field_simp
      have hns : 0 ≤ (n : ℝ) * s := by positivity
      calc 4608 * (n : ℝ) ^ 2 * q = 4608 * (n * s) := by rw [mul_assoc, h2]
        _ ≤ 1 / 4 * (k : ℝ) ^ 3 := by linarith
        _ ≤ (1 - q) ^ 2 * (k : ℝ) ^ 3 := mul_le_mul_of_nonneg_right h1 (by positivity)
    · have hq : q = p := by rw [hqdef, max_eq_left h]
      rw [hq]
      have : 0 ≤ (n : ℝ) ^ 2 * p := by positivity
      nlinarith
  · rcases le_or_gt q (1 / 2) with h | h
    · have : (k : ℝ) / 2 ≤ (1 - q) * k := by nlinarith
      linarith
    · obtain ⟨-, -, h2⟩ := hbig h
      have hqp' := (hbig h).1
      rw [hqp']; nlinarith
  · -- `q (1 - q) ≥ 1 / (2 √n)`.
    have h1 : 1 / (2 * s) ≤ q * (1 - q) := by
      rcases le_or_gt q (1 / 2) with h | h
      · have : q / 2 ≤ q * (1 - q) := by nlinarith
        have : 1 / (2 * s) = (1 / s) / 2 := by ring
        linarith
      · have : (1 - q) / 2 ≤ q * (1 - q) := by nlinarith
        have : 1 / (2 * s) = (1 / s) / 2 := by ring
        linarith
    have h2 : 18 * (n : ℝ) * (1 / (2 * s)) = 9 * s := by
      rw [← hss]; field_simp; ring
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 18 * n)
    linarith

/-- The characters are bounded by `√n`: `charMax q ≤ √n` when `1/√n ≤ q` and
`1/(1 - q) ≤ √n`. -/
theorem charMax_le {n : ℕ} {q : ℝ} (hq : 1 / √(n : ℝ) ≤ q) (hq1 : q < 1)
    (hq' : 1 / (1 - q) ≤ √(n : ℝ)) (hn : 1 ≤ n) : Biclique.charMax q ≤ √(n : ℝ) := by
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hq10 : 0 < 1 - q := by linarith
  unfold Biclique.charMax
  refine max_le ?_ ?_
  · have h1 : (1 - q) / q ≤ 1 / q := div_le_div_of_nonneg_right (by linarith) hq0.le
    have h2 : 1 / q ≤ √(n : ℝ) := by
      rw [div_le_iff₀ hq0]
      rw [div_le_iff₀ hs] at hq
      linarith
    linarith
  · have h1 : q / (1 - q) ≤ 1 / (1 - q) := div_le_div_of_nonneg_right (by linarith) hq10.le
    linarith

/-! ### The cleanup threshold -/

theorem delta1_ge (n k : ℕ) (hn : 1 ≤ n) :
    (k : ℝ) ^ 2 / (n * (Nat.log 2 n + 1)) ≤ Algorithm.delta1 n k := by
  unfold Algorithm.delta1
  have hb : 0 < n * (Nat.log 2 n + 1) := Nat.mul_pos (by omega) (by omega)
  have hlt := Nat.lt_div_mul_add (a := k * k) hb
  have hle : k * k ≤ (k * k / (n * (Nat.log 2 n + 1)) + 1) * (n * (Nat.log 2 n + 1)) := by
    rw [add_mul, one_mul]; omega
  have hb' : (0 : ℝ) < n * (Nat.log 2 n + 1) := by
    have : (0 : ℝ) < ((n * (Nat.log 2 n + 1) : ℕ) : ℝ) := by exact_mod_cast hb
    push_cast at this; exact this
  rw [div_le_iff₀ hb']
  have : ((k * k : ℕ) : ℝ) ≤ ((k * k / (n * (Nat.log 2 n + 1)) + 1 : ℕ) : ℝ) *
      ((n * (Nat.log 2 n + 1) : ℕ) : ℝ) := by exact_mod_cast hle
  push_cast at this ⊢
  nlinarith

theorem delta1_le (n k : ℕ) :
    (Algorithm.delta1 n k : ℝ) ≤ (k : ℝ) ^ 2 / (n * (Nat.log 2 n + 1)) + 1 := by
  unfold Algorithm.delta1
  push_cast
  have := Nat.cast_div_le (α := ℝ) (m := k * k) (n := n * (Nat.log 2 n + 1))
  push_cast at this
  rw [sq]
  linarith

/-- **The cleanup threshold**: `Δ ≤ k`, `2 n Δ ≤ k²` and
`2 n Δ / k² ≤ 2 / (log₂ n + 1) + 1 / (512 (log n)²)`. -/
theorem delta1_facts {n k : ℕ} (hn : 1 ≤ n) (hL : 3 ≤ Nat.log 2 n) (hlog : 1 ≤ Real.log n)
    (hk2 : 2 ≤ k) (hkn : k ≤ n) (hk : 1024 * n * Real.log n ^ 2 ≤ (k : ℝ) ^ 2) :
    Algorithm.delta1 n k ≤ k ∧ 2 * n * Algorithm.delta1 n k ≤ k ^ 2 ∧
      2 * n * (Algorithm.delta1 n k : ℝ) / (k : ℝ) ^ 2 ≤
        2 / (Nat.log 2 n + 1) + 1 / (512 * Real.log n ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL' : (3 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hL
  have hk0 : (0 : ℝ) < k := by have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
                               linarith
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hD := delta1_le n k
  set L : ℝ := Nat.log 2 n + 1 with hLdef
  have hL0 : 0 < L := by linarith
  have hlog2 : 0 < Real.log n ^ 2 := by positivity
  -- `2 n Δ / k² ≤ 2/L + 2n/k² ≤ 2/L + 1/(512 log² n)`.
  have h3 : 2 * n * (Algorithm.delta1 n k : ℝ) / (k : ℝ) ^ 2 ≤
      2 / L + 1 / (512 * Real.log n ^ 2) := by
    have e1 : 2 * n * ((k : ℝ) ^ 2 / (n * L) + 1) / (k : ℝ) ^ 2 = 2 / L + 2 * n / (k : ℝ) ^ 2 := by
      field_simp
    have e2 : 2 * (n : ℝ) / (k : ℝ) ^ 2 ≤ 1 / (512 * Real.log n ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc 2 * n * (Algorithm.delta1 n k : ℝ) / (k : ℝ) ^ 2 ≤
          2 * n * ((k : ℝ) ^ 2 / (n * L) + 1) / (k : ℝ) ^ 2 := by gcongr
      _ ≤ _ := by rw [e1]; linarith
  have h4 : 2 / L ≤ 1 / 2 := by rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have h5 : 1 / (512 * Real.log n ^ 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨?_, ?_, h3⟩
  · have : (k : ℝ) ^ 2 / (n * L) ≤ k / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h4k : 4 * (k : ℝ) ≤ n * L := by nlinarith
      have := mul_le_mul_of_nonneg_left h4k hk0.le
      nlinarith
    have : (Algorithm.delta1 n k : ℝ) ≤ k := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      linarith
    exact_mod_cast this
  · have h6 : 2 * n * (Algorithm.delta1 n k : ℝ) / (k : ℝ) ^ 2 ≤ 1 := by linarith
    rw [div_le_one (by positivity)] at h6
    exact_mod_cast h6

/-- **No large bicliques**: `log (400 n²) ≤ (1 - p) Δ`, from the size condition, for both
`p ≤ 1/2` and `p > 1/2`. -/
theorem nb_facts {n k : ℕ} {p : ℝ} (hn : 400 ≤ n) (hp1 : p < 1)
    (hlog : 1 ≤ Real.log n) (hL : (Nat.log 2 n : ℝ) + 1 ≤ 2 * Real.log n)
    (hnb : 9 * Real.log n ^ 4 ≤ 4096 * √(n : ℝ))
    (hc : 32768 * (n : ℝ) ^ 2 * p ≤ (k : ℝ) ^ 3 * (1 - p) ^ 2)
    (h1024 : 1024 * n * Real.log n ^ 2 ≤ (k : ℝ) ^ 2) (hk : √(n : ℝ) ≤ k) :
    Real.log (400 * (n : ℝ) ^ 2) ≤ (1 - p) * Algorithm.delta1 n k := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hD := delta1_ge n k hn1
  set L : ℝ := Nat.log 2 n + 1 with hLdef
  have hL0 : 0 < L := by positivity
  have hq0 : 0 < 1 - p := by linarith
  have hlogn : Real.log (400 * (n : ℝ) ^ 2) ≤ 3 * Real.log n := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have : Real.log 400 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    push_cast; linarith
  have hD0 : 0 ≤ (k : ℝ) ^ 2 / (n * L) := by positivity
  have hkey : 3 * Real.log n ≤ (1 - p) * ((k : ℝ) ^ 2 / (n * L)) := by
    rcases le_or_gt p (1 / 2) with h | h
    · -- `(1 - p) Δ ≥ k² / (2 n L) ≥ 1024 n log² n / (4 n log n) = 256 log n`.
      have h1 : (k : ℝ) ^ 2 / (n * L) / 2 ≤ (1 - p) * ((k : ℝ) ^ 2 / (n * L)) := by nlinarith
      have h2 : 3 * Real.log n ≤ (k : ℝ) ^ 2 / (n * L) / 2 := by
        rw [div_div, le_div_iff₀ (by positivity)]
        have : n * L * 2 * (3 * Real.log n) ≤ n * (2 * Real.log n) * 2 * (3 * Real.log n) := by
          gcongr
        nlinarith
      linarith
    · -- `((1 - p) Δ)² ≥ 16384 k / L² ≥ 4096 √n / log² n ≥ 9 log² n`.
      have hc' : 16384 * (n : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 * (1 - p) ^ 2 := by nlinarith
      have hsq : (3 * Real.log n) ^ 2 ≤ ((1 - p) * ((k : ℝ) ^ 2 / (n * L))) ^ 2 := by
        have e : ((1 - p) * ((k : ℝ) ^ 2 / (n * L))) ^ 2 =
            ((k : ℝ) ^ 3 * (1 - p) ^ 2) * k / ((n : ℝ) ^ 2 * L ^ 2) := by
          field_simp
        rw [e, le_div_iff₀ (by positivity)]
        have hL2 : L ^ 2 ≤ 4 * Real.log n ^ 2 := by nlinarith
        have h1 : (3 * Real.log n) ^ 2 * ((n : ℝ) ^ 2 * L ^ 2) ≤
            9 * Real.log n ^ 2 * (n : ℝ) ^ 2 * (4 * Real.log n ^ 2) := by
          have e : (3 * Real.log n) ^ 2 * ((n : ℝ) ^ 2 * L ^ 2) =
              (9 * Real.log n ^ 2 * (n : ℝ) ^ 2) * L ^ 2 := by ring
          rw [e]; exact mul_le_mul_of_nonneg_left hL2 (by positivity)
        have h2 : 9 * Real.log n ^ 2 * (n : ℝ) ^ 2 * (4 * Real.log n ^ 2) =
            4 * (n : ℝ) ^ 2 * (9 * Real.log n ^ 4) := by ring
        have h3 : 4 * (n : ℝ) ^ 2 * (9 * Real.log n ^ 4) ≤ 4 * (n : ℝ) ^ 2 * (4096 * √n) := by
          gcongr
        have h4 : 4 * (n : ℝ) ^ 2 * (4096 * √n) ≤ 16384 * (n : ℝ) ^ 2 * k := by
          have : 0 ≤ (n : ℝ) ^ 2 := by positivity
          nlinarith
        have h5 : 16384 * (n : ℝ) ^ 2 * k ≤ ((k : ℝ) ^ 3 * (1 - p) ^ 2) * k := by
          have : (0 : ℝ) ≤ k := (Real.sqrt_nonneg _).trans hk
          nlinarith
        linarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 hsq
  calc Real.log (400 * (n : ℝ) ^ 2) ≤ 3 * Real.log n := hlogn
    _ ≤ (1 - p) * ((k : ℝ) ^ 2 / (n * L)) := hkey
    _ ≤ (1 - p) * Algorithm.delta1 n k := mul_le_mul_of_nonneg_left hD hq0.le

/-! ### Large `n` -/

open Filter Topology

/-- The exponent `ℓ` of the moment method: `r = 2^ℓ`, with `ℓ = ⌊log₂ ⌊log₂ n⌋⌋ + 2`, so that
`2 log₂ n < r ≤ 4 log₂ n`. -/
def ell (n : ℕ) : ℕ := Nat.log 2 (Nat.log 2 n) + 2

/-- The factor the solver's error must beat: `(20n + 3)^12 + 1000 (n + 1)^3`. -/
noncomputable def zOf (n : ℕ) : ℝ := (20 * (n : ℝ) + 3) ^ 12 + 1000 * ((n : ℝ) + 1) ^ 3

/-- The relative excess of the list over `n / k`: `2 / (log₂ n + 1) + 1 / (512 (log n)²)`. -/
noncomputable def δ1 (n : ℕ) : ℝ := 2 / (Nat.log 2 n + 1) + 1 / (512 * Real.log n ^ 2)

/-- The conditions on `n` alone. -/
structure Large (n : ℕ) : Prop where
  n_ge : 1100 ≤ n
  log_ge : 1 ≤ Real.log n
  L2_ge : 3 ≤ Nat.log 2 n
  L2_le : (Nat.log 2 n : ℝ) + 1 ≤ 2 * Real.log n
  rmt : (2 * 2 ^ ell n + 1 : ℝ) ^ 4 ≤ √(n : ℝ)
  rmt_prob : (n : ℝ) / 2 ^ (2 ^ ell n) ≤ 1 / 400
  nonnbr : (n : ℝ) * Real.exp (-(√(n : ℝ) / 16)) ≤ 1 / 400
  nb : 9 * Real.log n ^ 4 ≤ 4096 * √(n : ℝ)
  tiny : ((Algorithm.accη n 0 : ℝ) + Algorithm.accγ n 0) * 2 ^ (2 * (n + 2) ^ 3) * zOf n ≤ 1
  lam : (Algorithm.accγ n 0 : ℝ) / (Algorithm.accη n 0 + Algorithm.accγ n 0) * (5 * n) ≤ 1 / 8

theorem natLog_le_log {n : ℕ} (hn : 1 ≤ n) : (Nat.log 2 n : ℝ) ≤ 3 / 2 * Real.log n := by
  have h1 : (2 : ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h2 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at this
  have h3 : 2 / 3 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h0 : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  nlinarith

theorem log_le_natLog {n : ℕ} (hn : 1 ≤ n) : Real.log n ≤ (Nat.log 2 n : ℝ) + 1 := by
  have h1 : (n : ℝ) < 2 ^ (Nat.log 2 n + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two n
  have h2 := Real.log_lt_log (by exact_mod_cast hn) h1
  rw [Real.log_pow] at h2
  have h3 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  push_cast at h2
  have : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by positivity
  nlinarith

theorem two_pow_ell_le {n : ℕ} (hn : 2 ≤ n) : 2 ^ ell n ≤ 4 * Nat.log 2 n := by
  have hL : Nat.log 2 n ≠ 0 := by
    have := Nat.le_log_of_pow_le one_lt_two (show 2 ^ 1 ≤ n by omega); omega
  have := Nat.pow_log_le_self 2 hL
  rw [ell, pow_add]
  omega

theorem lt_two_pow_ell (n : ℕ) : 2 * Nat.log 2 n < 2 ^ ell n := by
  have := Nat.lt_pow_succ_log_self one_lt_two (Nat.log 2 n)
  rw [ell, pow_add, pow_succ] at *
  omega

theorem eventually_sqrt_ge (c : ℝ) : ∀ᶠ n : ℕ in atTop, c ≤ √(n : ℝ) := by
  have h := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c
  exact h

theorem eventually_log_ge (c : ℝ) : ∀ᶠ n : ℕ in atTop, c ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c

/-- `log n ≤ c n^(1/8)` eventually, and `(n^(1/8))^4 = √n`. -/
theorem eventually_log_pow_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (Real.log n / c) ^ 4 ≤ √(n : ℝ) := by
  filter_upwards [Assembly.eventually_log_le hc (by norm_num : (0 : ℝ) < 1 / 8),
    eventually_ge_atTop 1] with n hn hn1
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have h1 : Real.log n / c ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by rw [div_le_iff₀ hc]; linarith
  have h2 : ((n : ℝ) ^ (1 / 8 : ℝ)) ^ 4 = √(n : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  calc (Real.log n / c) ^ 4 ≤ ((n : ℝ) ^ (1 / 8 : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) h1 4
    _ = √(n : ℝ) := h2

theorem eventually_nonnbr :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) * Real.exp (-(√(n : ℝ) / 16)) ≤ 1 / 400 := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
    ((tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 16)).comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  filter_upwards [h.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 102400))] with n hn
  simp only [Function.comp_apply, id] at hn
  have hs : (√(n : ℝ)) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have e : (n : ℝ) * Real.exp (-(√(n : ℝ) / 16)) =
      256 * ((√(n : ℝ) / 16) ^ 2 * Real.exp (-(√(n : ℝ) / 16))) := by
    rw [div_pow, hs]; ring
  rw [e]
  linarith

theorem eventually_tiny :
    ∀ᶠ n : ℕ in atTop, ((Algorithm.accη n 0 : ℝ) + Algorithm.accγ n 0) * 2 ^ (2 * (n + 2) ^ 3) *
      zOf n ≤ 1 := by
  set K : ℝ := 23 ^ 12 + 8000
  have h := Assembly.eventually_pow_div_two_pow_le 12 (by positivity : (0 : ℝ) < 1 / (2 * K))
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hZ : zOf n ≤ K * (n : ℝ) ^ 12 := by
    unfold zOf
    have h1 : (20 * (n : ℝ) + 3) ^ 12 ≤ (23 * n) ^ 12 := pow_le_pow_left₀ (by positivity)
      (by linarith) 12
    have h2 : ((n : ℝ) + 1) ^ 3 ≤ (2 * n) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    have h3 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 12 := pow_le_pow_right₀ hn1' (by norm_num)
    have : (23 * (n : ℝ)) ^ 12 = 23 ^ 12 * (n : ℝ) ^ 12 := by ring
    have : (2 * (n : ℝ)) ^ 3 = 8 * (n : ℝ) ^ 3 := by ring
    nlinarith
  have hZ0 : 0 ≤ zOf n := by unfold zOf; positivity
  calc ((Algorithm.accη n 0 : ℝ) + Algorithm.accγ n 0) * 2 ^ (2 * (n + 2) ^ 3) * zOf n
      ≤ 2 / 2 ^ n * (K * (n : ℝ) ^ 12) :=
        mul_le_mul (Assembly.tiny_le n 0) hZ hZ0 (by positivity)
    _ = 2 * K * ((n : ℝ) ^ 12 / 2 ^ n) := by ring
    _ ≤ 2 * K * (1 / (2 * K)) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = 1 := by have hK : K ≠ 0 := by positivity
                field_simp

/-- **Eventually all the conditions hold.** -/
theorem eventually_large : ∀ᶠ n : ℕ in atTop, Large n := by
  filter_upwards [eventually_ge_atTop 1100, eventually_log_ge 2, eventually_log_pow_le
    (by norm_num : (0 : ℝ) < 1 / 13), eventually_log_pow_le (by norm_num : (0 : ℝ) < 1),
    eventually_nonnbr, eventually_tiny, Assembly.eventually_lam 0] with n hn hlog hrmt hnb hnon
      htiny hlam
  have hn1 : 1 ≤ n := by omega
  have hL3 : 3 ≤ Nat.log 2 n := Nat.le_log_of_pow_le one_lt_two (by norm_num; omega)
  have hLle := natLog_le_log hn1
  refine ⟨hn, by linarith, hL3, by linarith, ?_, ?_, hnon, ?_, htiny, hlam⟩
  · -- `2 · 2^ℓ + 1 ≤ 8 log₂ n + 1 ≤ 13 log n`.
    have h1 : (2 ^ ell n : ℝ) ≤ 4 * Nat.log 2 n := by exact_mod_cast two_pow_ell_le (by omega)
    have h2 : (2 * 2 ^ ell n + 1 : ℝ) ≤ Real.log n / (1 / 13) := by
      rw [div_div_eq_mul_div, div_one]; linarith
    exact (pow_le_pow_left₀ (by positivity) h2 4).trans hrmt
  · -- `2^r > n² / 2`.
    have h1 := lt_two_pow_ell n
    have h2 : (n : ℝ) < 2 ^ (Nat.log 2 n + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two n
    have h3 : (2 : ℝ) ^ (2 * Nat.log 2 n + 1) ≤ 2 ^ (2 ^ ell n) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : (n : ℝ) ^ 2 < 2 * 2 ^ (2 * Nat.log 2 n + 1) := by
      have : (n : ℝ) ^ 2 < (2 ^ (Nat.log 2 n + 1)) ^ 2 :=
        pow_lt_pow_left₀ h2 (by positivity) (by norm_num)
      rw [← pow_mul] at this
      have e : (2 : ℝ) * 2 ^ (2 * Nat.log 2 n + 1) = 2 ^ ((Nat.log 2 n + 1) * 2) := by
        rw [← pow_succ']; ring_nf
      linarith
    have hn' : (1100 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · have : (Real.log n / 1) ^ 4 = Real.log n ^ 4 := by rw [div_one]
    rw [this] at hnb
    have : (0 : ℝ) ≤ √(n : ℝ) := Real.sqrt_nonneg _
    linarith

theorem tendsto_δ1 : Tendsto δ1 atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ ↦ 2 / Real.log n + 1 / (512 * Real.log n ^ 2)) atTop (𝓝 0) := by
    have a : Tendsto (fun n : ℕ ↦ (Real.log n)⁻¹) atTop (𝓝 0) := hlog.inv_tendsto_atTop
    have b := (a.const_mul 2).add ((a.pow 2).const_mul (1 / 512))
    simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at b
    refine b.congr fun n ↦ ?_
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
  · filter_upwards with n
    unfold δ1
    positivity
  · filter_upwards [eventually_log_ge 1, eventually_ge_atTop 1] with n hn hn1
    unfold δ1
    have h := log_le_natLog hn1
    have : 2 / ((Nat.log 2 n : ℝ) + 1) ≤ 2 / Real.log n :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) h
    linarith

end BKS23.Size1
