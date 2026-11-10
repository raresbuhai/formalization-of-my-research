module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdNorms

/-! Parameter-only bit envelopes for the rounded high-degree SUB payload. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdBits

open Common Rounding _root_.ABBKS26.Tree Sources Builders
open _root_.ABBKS26.Schedule.EncodingBounds
open Encoding (encRat)

noncomputable section

theorem ceiling {b : ℕ} {q : ℚ} (h : RatBound b q) : ⌈q⌉₊ ≤ 2 ^ b :=
  Nat.ceil_le.mpr (by exact_mod_cast (le_abs_self q).trans h.magnitude)

theorem nat_bound (m b : ℕ) (hm : m ≤ 2 ^ b) : RatBound b (m : ℚ) := by
  constructor
  · simpa only [abs_of_nonneg (by positivity : (0 : ℚ) ≤ m)] using
      (show (m : ℚ) ≤ 2 ^ b by exact_mod_cast hm)
  · simpa only [Rat.den_natCast] using Nat.one_le_two_pow

theorem nat_coarse (m B : ℕ) (hm : m ≤ B) : RatBound B (m : ℚ) :=
  nat_bound m B (hm.trans (Nat.lt_two_pow_self (n := B)).le)

theorem hundred_pow (B e : ℕ) (hB : 100 ≤ B) : 100 * B ^ e ≤ B ^ (e + 1) := by
  rw [pow_succ]
  nlinarith only [Nat.mul_le_mul_right (B ^ e) hB]

theorem power_linear (B d e f : ℕ) (hB : 1 ≤ B) (he : e ≤ f) :
    B ^ e ≤ B ^ f * (d + 2) :=
  (Nat.pow_le_pow_right hB he).trans (Nat.le_mul_of_pos_right _ (by omega))

theorem dimension_linear (B d e : ℕ) (hB : 1 ≤ B) :
    d ≤ B ^ e * (d + 2) :=
  (by omega : d ≤ d + 2).trans (Nat.le_mul_of_pos_left _ (by positivity))

theorem tolerance (a : Args) (B : ℕ) (hB : 100 ≤ B)
    (hβ : 0 ≤ field a 10 ∧ field a 10 ≤ 1) (hden : (field a 10).den ≤ B) :
    RatBound (B ^ 2) (IdPayload.tolerance a) := by
  have hb : RatBound B (field a 10) :=
    ⟨(by rw [abs_of_nonneg hβ.1]; exact hβ.2.trans (one_le_pow₀ (by norm_num))),
      hden.trans (Nat.lt_two_pow_self (n := B)).le⟩
  have h25 : RatBound 5 25 := by constructor <;> norm_num
  exact ((hb.div h25).pow 8).mono (by nlinarith only [hB])

theorem systemError (a : Args) (B : ℕ) (hB : 100 ≤ B)
    (ht : IdInput.degree a ≤ B)
    (hβ : 0 ≤ field a 10 ∧ field a 10 ≤ 1) (hden : (field a 10).den ≤ B) :
    RatBound (B ^ 3) (IdPayload.systemError a) := by
  have h3 : RatBound 2 3 := by constructor <;> norm_num
  have h64 : RatBound 6 64 := by constructor <;> norm_num
  have h4 : RatBound 2 4 := by constructor <;> norm_num
  have htQ := nat_coarse (IdInput.degree a) B ht
  have hβb : RatBound B (field a 10) :=
    ⟨(by rw [abs_of_nonneg hβ.1]; exact hβ.2.trans (one_le_pow₀ (by norm_num))),
      hden.trans (Nat.lt_two_pow_self (n := B)).le⟩
  have h25 : RatBound 5 25 := by constructor <;> norm_num
  have hε := (hβb.div h25).pow 8
  have hb := ((((hε.pow 2).div h3).div (h64.mul htQ)).pow
    (4 * IdInput.degree a)).div h4
  apply hb.mono
  have hmul : B * IdInput.degree a ≤ B ^ 2 := by
    nlinarith only [Nat.mul_le_mul_left B ht]
  have hpow := hundred_pow B 2 hB
  nlinarith only [ht, hB, hmul, hpow]


theorem momentError (a : Args) (B : ℕ) (hB : 100 ≤ B)
    (ht : IdInput.degree a ≤ B)
    (hβ : 0 ≤ field a 10 ∧ field a 10 ≤ 1) (hden : (field a 10).den ≤ B) :
    RatBound (B ^ 4) (IdPayload.momentError a) := by
  have h8 : RatBound 3 8 := by constructor <;> norm_num
  have hb := (systemError a B hB ht hβ hden).div
    ((h8.mul (nat_coarse (IdInput.degree a) B ht)).pow (4 * IdInput.degree a + 2))
  apply hb.mono
  have hB2 : B ^ 2 ≤ B ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hB1 : B ≤ B ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have hB0 : 1 ≤ B ^ 3 := one_le_pow₀ (by omega)
  calc
    _ ≤ B ^ 3 + 2 * ((3 + B) * (4 * B + 2)) := by gcongr
    _ ≤ 100 * B ^ 3 := by nlinarith only [hB2, hB1, hB0]
    _ ≤ _ := hundred_pow B 3 hB

theorem precision (a : Args) (B : ℕ) (hB : 100 ≤ B)
    (ht : IdInput.degree a ≤ B)
    (hβ : 0 ≤ field a 10 ∧ field a 10 ≤ 1) (hden : (field a 10).den ≤ B) :
    IdPayload.precision a ≤ B ^ 5 * (a.1.1 + 2) := by
  have hη := momentError a B hB ht hβ hden
  have hp := (nat_coarse (a.1.1 + 1) (a.1.1 + 1) le_rfl).pow (4 * IdInput.degree a)
  have hb := Nat.clog_le_of_le_pow (ceiling (hp.div hη))
  simp only [Nat.cast_add, Nat.cast_one] at hb
  change Nat.clog 2 ⌈(a.1.1 + 1 : ℚ) ^ (4 * IdInput.degree a) /
    IdPayload.momentError a⌉₊ ≤ _ at hb
  change Nat.clog 2 ⌈(a.1.1 + 1 : ℚ) ^ (4 * IdInput.degree a) /
    IdPayload.momentError a⌉₊ + 2 ≤ _
  have hB4 : B ≤ B ^ 4 := le_self_pow₀ (by omega) (by norm_num)
  have hB40 : 1 ≤ B ^ 4 := one_le_pow₀ (by omega)
  have hcoef : 4 * B + 2 * B ^ 4 + 2 ≤ 100 * B ^ 4 := by omega
  calc
    _ ≤ (a.1.1 + 1) * (4 * IdInput.degree a) + 2 * B ^ 4 + 2 := by omega
    _ = (a.1.1 + 1) * (4 * IdInput.degree a) + (2 * B ^ 4 + 2) := by ring
    _ ≤ (a.1.1 + 2) * (4 * B) + (2 * B ^ 4 + 2) * (a.1.1 + 2) :=
      Nat.add_le_add (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left 4 ht))
        (Nat.le_mul_of_pos_right _ (by omega))
    _ = (4 * B + 2 * B ^ 4 + 2) * (a.1.1 + 2) := by ring
    _ ≤ (100 * B ^ 4) * (a.1.1 + 2) := Nat.mul_le_mul_right _ hcoef
    _ ≤ _ := Nat.mul_le_mul_right _ (hundred_pow B 4 hB)

theorem size (a : Args) (B : ℕ) (hB : 100 ≤ B)
    (ht : IdInput.degree a ≤ B) (hA : ⌈8 / field a 0⌉₊ ≤ B)
    (hβ : 0 ≤ field a 10 ∧ field a 10 ≤ 1) (hden : (field a 10).den ≤ B) :
    RatBound (B ^ 6 * (a.1.1 + 2)) (IdPayload.size a) := by
  have hp := precision a B hB ht hβ hden
  have hs := systemError a B hB ht hβ hden
  have hE := nat_bound ⌈1 / IdPayload.systemError a⌉₊ (2 * B ^ 3)
    (by simpa only [one_div] using ceiling hs.inv)
  have h64 : RatBound 6 64 := by constructor <;> norm_num
  have htwo := nat_bound (2 ^ IdPayload.precision a) (IdPayload.precision a) le_rfl
  have hb := ((((htwo.mul h64).mul
    ((nat_coarse (a.1.1 + 1) (a.1.1 + 1) le_rfl).pow 2)).mul
      (nat_coarse (IdInput.degree a) B ht)).mul (nat_coarse _ B hA)).mul hE
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] at hb
  apply hb.mono
  have hB3 : B ≤ B ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have hB35 : B ^ 3 ≤ B ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hB50 : 1 ≤ B ^ 5 := one_le_pow₀ (by omega)
  have hh := Nat.mul_le_mul_right (a.1.1 + 2) (hundred_pow B 5 hB)
  have h1 := power_linear B a.1.1 1 5 (by omega) (by norm_num)
  have h3 := power_linear B a.1.1 3 5 (by omega) (by norm_num)
  have h0 := power_linear B a.1.1 0 5 (by omega) (by norm_num)
  have hd := dimension_linear B a.1.1 5 (by omega)
  apply le_trans _ hh
  nlinarith only [hp, h1, h3, h0, hd, Nat.zero_le (B ^ 5 * (a.1.1 + 2))]

theorem exponent (a : Args) (B : ℕ) (hB : 100 ≤ B)
    (ht : IdInput.degree a ≤ B) (hA : ⌈8 / field a 0⌉₊ ≤ B)
    (hβ : 0 ≤ field a 10 ∧ field a 10 ≤ 1) (hden : (field a 10).den ≤ B) :
    IdPayload.exponent a ≤ B ^ 9 * (a.1.1 + 2) := by
  have h2 : RatBound 1 2 := by constructor <;> norm_num
  have hb := (h2.mul ((size a B hB ht hA hβ hden).pow (4 * IdInput.degree a))).bits
  change IdPayload.exponent a ≤ _ at hb
  have hmul : B ^ 6 * IdInput.degree a ≤ B ^ 7 := by
    exact (Nat.mul_le_mul_left (B ^ 6) ht).trans_eq (by ring)
  have hm := Nat.mul_le_mul_right (a.1.1 + 2) hmul
  have h1 : 1 ≤ B ^ 7 * (a.1.1 + 2) :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  calc
    _ ≤ 6 * (1 + 4 * B ^ 7 * (a.1.1 + 2)) + 6 := by nlinarith only [hb, hm]
    _ ≤ 100 * B ^ 7 * (a.1.1 + 2) := by nlinarith only [h1]
    _ ≤ B ^ 8 * (a.1.1 + 2) := Nat.mul_le_mul_right _ (hundred_pow B 7 hB)
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))


theorem norm_bound (d K m E V : ℕ) (ε M : ℚ)
    (hε : RatBound E ε) (hM : RatBound V M) :
    RatBound ((m + 1) + 100 * (d + 1) * (K + 1) + 10 * V + 10 * E + 100)
      (IdNorms.norm d K m ε M) := by
  have hd := nat_coarse (d + 1) (d + 1) le_rfl
  have hm := nat_coarse (m + 1) (m + 1) le_rfl
  have h2 : RatBound 1 2 := by constructor <;> norm_num
  have h4 : RatBound 2 4 := by constructor <;> norm_num
  have hb := hd.pow K
  have hfirst := hm.mul (((h2.mul (hM.add RatBound.one)).mul
    (hd.pow (2 * K))).mul (hb.pow 5))
  have hsecond := hb.mul ((hb.add RatBound.one).pow 2)
  have hthird := ((hd.pow 2).add h2).pow 2
  have hr := (((hfirst.add hsecond).add hthird).div (h4.mul hε)).add RatBound.one
  simp only [Nat.cast_add, Nat.cast_one] at hr
  apply hr.mono
  nlinarith

theorem ball_bound (d e m E V : ℕ) (ε M : ℚ)
    (hε : RatBound E ε) (hM : RatBound V M) :
    RatBound (100 * (d + 1) * (e + 1) ^ 3 + (m + 1) + 10 * V + 10 * E + 100)
      (IdNorms.ball d e m ε M) := by
  have hd := nat_coarse (d + 1) (d + 1) le_rfl
  have hm := nat_coarse (m + 1) (m + 1) le_rfl
  have he := nat_coarse e e le_rfl
  have he' := nat_coarse (e + 1) (e + 1) le_rfl
  have h2 : RatBound 1 2 := by constructor <;> norm_num
  have h6 : RatBound 3 6 := by constructor <;> norm_num
  have hI := he'.pow ((e + 1) ^ 2)
  have hinside := ((h2.mul hM).add (h2.mul hε)).add (h6.mul (hd.pow 2))
  have hb := h2.add ((((((hm.mul (hd.pow e)).mul (hI.pow (2 * d))).mul
    (he'.pow d)).mul (he'.pow d)).mul hinside).mul (he.pow (2 * e)))
  simp only [Nat.cast_add, Nat.cast_one] at hb
  apply hb.mono
  ring_nf
  omega

theorem ident (a : Args) (B : ℕ) (hB : 100 ≤ B)
    (ht : IdInput.degree a ≤ B) (hA : ⌈8 / field a 0⌉₊ ≤ B)
    (hβ : 0 ≤ field a 10 ∧ field a 10 ≤ 1) (hden : (field a 10).den ≤ B) :
    RatBound (B ^ 10 * (a.1.1 + 2)) (IdNorms.ident a) := by
  have hs := size a B hB ht hA hβ hden
  have ht' := nat_coarse (2 * IdInput.degree a + 1) (2 * B + 1) (by omega)
  have hb := ((hs.pow 2).pow (29 * IdInput.degree a)).mul
    (RatBound.one.add (ht'.mul (hs.pow (16 * IdInput.degree a + 1))))
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hb
  apply hb.mono
  have hm : B ^ 6 * IdInput.degree a ≤ B ^ 7 :=
    (Nat.mul_le_mul_left (B ^ 6) ht).trans_eq (by ring)
  have hm' := Nat.mul_le_mul_right (a.1.1 + 2) hm
  have h6 := power_linear B a.1.1 6 7 (by omega) (by norm_num)
  have h1 := power_linear B a.1.1 1 7 (by omega) (by norm_num)
  have h0 := power_linear B a.1.1 0 7 (by omega) (by norm_num)
  have h67 := Nat.mul_le_mul_right (a.1.1 + 2)
    (Nat.pow_le_pow_right (by omega : 1 ≤ B) (by norm_num : 6 ≤ 7))
  calc
    _ ≤ 100 * B ^ 7 * (a.1.1 + 2) := by nlinarith only [hm', h1, h0, h67]
    _ ≤ B ^ 8 * (a.1.1 + 2) := Nat.mul_le_mul_right _ (hundred_pow B 7 hB)
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))

theorem projection (a : Args) (B : ℕ) (hB : 100 ≤ B)
    (ht : IdInput.degree a ≤ B) (hA : ⌈8 / field a 0⌉₊ ≤ B)
    (hβ : 0 ≤ field a 10 ∧ field a 10 ≤ 1) (hden : (field a 10).den ≤ B) :
    RatBound (B ^ 12 * (a.1.1 + 2)) (IdNorms.projection a) := by
  have hi := ident a B hB ht hA hβ hden
  have hε := tolerance a B hB hβ hden
  have hd := nat_coarse a.1.1 a.1.1 le_rfl
  have h2 : RatBound 1 2 := by constructor <;> norm_num
  have h3 : RatBound 2 3 := by constructor <;> norm_num
  have hb := RatBound.one.max ((hi.add ((h2.add (hε.div h3)).mul (hd.pow 2))).div
    (hε.div h3))
  apply hb.mono
  apply max_le (by positivity)
  have h2' := power_linear B a.1.1 2 10 (by omega) (by norm_num)
  have h0 := power_linear B a.1.1 0 10 (by omega) (by norm_num)
  have hd' := dimension_linear B a.1.1 10 (by omega)
  calc
    _ ≤ 100 * B ^ 10 * (a.1.1 + 2) := by nlinarith only [h2', h0, hd']
    _ ≤ B ^ 11 * (a.1.1 + 2) := Nat.mul_le_mul_right _ (hundred_pow B 10 hB)
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))

theorem complement (a : Args) (B : ℕ) (hB : 100 ≤ B)
    (ht : IdInput.degree a ≤ B) (hA : ⌈8 / field a 0⌉₊ ≤ B)
    (hβ : 0 ≤ field a 10 ∧ field a 10 ≤ 1) (hden : (field a 10).den ≤ B) :
    RatBound (B ^ 10 * (a.1.1 + 2)) (IdNorms.complement a) := by
  have hb := RatBound.one.max ((size a B hB ht hA hβ hden).pow (20 * IdInput.degree a))
  apply hb.mono
  apply max_le (by positivity)
  have hm : B ^ 6 * IdInput.degree a ≤ B ^ 7 :=
    (Nat.mul_le_mul_left (B ^ 6) ht).trans_eq (by ring)
  have hm' := Nat.mul_le_mul_right (a.1.1 + 2) hm
  calc
    _ ≤ 100 * B ^ 7 * (a.1.1 + 2) := by
      nlinarith only [hm', Nat.zero_le (B ^ 7 * (a.1.1 + 2))]
    _ ≤ B ^ 8 * (a.1.1 + 2) := Nat.mul_le_mul_right _ (hundred_pow B 7 hB)
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))

theorem normInput (a : Args) (B : ℕ) (hB : 100 ≤ B)
    (ht : IdInput.degree a ≤ B) (hA : ⌈8 / field a 0⌉₊ ≤ B)
    (hβ : 0 ≤ field a 10 ∧ field a 10 ≤ 1) (hden : (field a 10).den ≤ B) :
    RatBound (B ^ 20 * (a.1.1 + 2)) (IdNorms.normInput a) := by
  have hb := norm_bound a.1.1 (8 * IdInput.degree a) (2 * IdInput.degree a + 1) _ _ _ _
    (tolerance a B hB hβ hden) (complement a B hB ht hA hβ hden)
  apply hb.mono
  have hgeom : 100 * (a.1.1 + 1) * (8 * IdInput.degree a + 1) ≤
      B ^ 3 * (a.1.1 + 2) := by
    have hh : 900 * B ≤ B ^ 3 := by
      have h1 : 100 * B ≤ B ^ 2 := by simpa only [pow_one] using hundred_pow B 1 hB
      have h2 : 100 * B ^ 2 ≤ B ^ 3 := hundred_pow B 2 hB
      omega
    calc
      _ ≤ (900 * B) * (a.1.1 + 2) := by nlinarith only [ht, hB]
      _ ≤ _ := Nat.mul_le_mul_right _ hh
  have hg := hgeom.trans (Nat.mul_le_mul_right (a.1.1 + 2)
    (Nat.pow_le_pow_right (by omega : 1 ≤ B) (by norm_num : 3 ≤ 10)))
  have h2' := power_linear B a.1.1 2 10 (by omega) (by norm_num)
  have h1 := power_linear B a.1.1 1 10 (by omega) (by norm_num)
  have h0 := power_linear B a.1.1 0 10 (by omega) (by norm_num)
  calc
    _ ≤ 100 * B ^ 10 * (a.1.1 + 2) := by nlinarith only [hg, ht, h2', h1, h0, hB]
    _ ≤ B ^ 11 * (a.1.1 + 2) := Nat.mul_le_mul_right _ (hundred_pow B 10 hB)
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))

theorem ballInput (a : Args) (B : ℕ) (hB : 100 ≤ B)
    (ht : IdInput.degree a ≤ B) (hA : ⌈8 / field a 0⌉₊ ≤ B)
    (hβ : 0 ≤ field a 10 ∧ field a 10 ≤ 1) (hden : (field a 10).den ≤ B) :
    RatBound (B ^ 20 * (a.1.1 + 2)) (IdNorms.ballInput a) := by
  have hb := ball_bound a.1.1 (4 * IdInput.degree a) (2 * IdInput.degree a + 1) _ _ _ _
    (tolerance a B hB hβ hden) (projection a B hB ht hA hβ hden)
  apply hb.mono
  have he : (4 * IdInput.degree a + 1) ^ 3 ≤ (5 * B) ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  have hgeom : 100 * (a.1.1 + 1) * (4 * IdInput.degree a + 1) ^ 3 ≤
      B ^ 6 * (a.1.1 + 2) := by
    have hh : 12500 * B ^ 3 ≤ B ^ 6 := by
      have h3 : 100 * B ^ 3 ≤ B ^ 4 := hundred_pow B 3 hB
      have h4 : 100 * B ^ 4 ≤ B ^ 5 := hundred_pow B 4 hB
      have h5 : 100 * B ^ 5 ≤ B ^ 6 := hundred_pow B 5 hB
      omega
    calc
      _ ≤ 100 * (a.1.1 + 1) * (5 * B) ^ 3 := Nat.mul_le_mul_left _ he
      _ = (12500 * B ^ 3) * (a.1.1 + 1) := by ring
      _ ≤ (12500 * B ^ 3) * (a.1.1 + 2) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ _ := Nat.mul_le_mul_right _ hh
  have hg := hgeom.trans (Nat.mul_le_mul_right (a.1.1 + 2)
    (Nat.pow_le_pow_right (by omega : 1 ≤ B) (by norm_num : 6 ≤ 12)))
  have h2' := power_linear B a.1.1 2 12 (by omega) (by norm_num)
  have h1 := power_linear B a.1.1 1 12 (by omega) (by norm_num)
  have h0 := power_linear B a.1.1 0 12 (by omega) (by norm_num)
  calc
    _ ≤ 100 * B ^ 12 * (a.1.1 + 2) := by nlinarith only [hg, ht, h2', h1, h0, hB]
    _ ≤ B ^ 13 * (a.1.1 + 2) := Nat.mul_le_mul_right _ (hundred_pow B 12 hB)
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))


theorem inputs {n d : ℕ} (k : ℕ) (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k)
    (hβ : 0 ≤ (ps h).subspaceAccuracy ∧ (ps h).subspaceAccuracy ≤ 1) :
    let a := (args k ps x h P, fuel)
    let B := idReserve k (ps h)
    100 ≤ B ∧ IdInput.degree a ≤ B ∧ ⌈8 / field a 0⌉₊ ≤ B ∧
      (0 ≤ field a 10 ∧ field a 10 ≤ 1) ∧ (field a 10).den ≤ B ∧
      IdCov.N_pack (field a 10) k ≤ B := by
  simp only [IdInput.degree, field_args _ _ _ _ _ _ hh, paramsList,
    List.getD_cons_zero, List.getD_cons_succ]
  dsimp only [idReserve]
  exact ⟨by omega, by omega, by omega, hβ, by omega, by omega⟩


end

end ABBKS26.Assembly.Exec.RefineSynth.IdBits
