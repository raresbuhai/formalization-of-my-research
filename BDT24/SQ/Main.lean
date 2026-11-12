module

public import BDT24.SQ.Corr
public import BDT24.SQ.Holder
public import BDT24.LowDeg.Overlap
import BDT24.SQ.Main.Bounds
import BDT24.Prob.Gauss.Spike

/-!
# Theorem C.6

`BDT24.SQ.sq_negSPCA_main`: the statement of `BDT24.sq_negSPCA` in `BDT24/Challenge.lean`.

Write `τ = ⟨x_u, x_v⟩ ∈ [-1, 1]` and `g = ⟨D̄_u, D̄_v⟩ - 1 = (1 - θ² τ²)^(-1/2) - 1 ≥ 0`
(`BDT24.SQ.pairCorr_eq`). Pointwise, `g ≤ 2 τ²` when `|τ| ≤ 1/2`, and `g ≤ k + 2` always since
`1 - θ² τ² ≥ 1 - θ ≥ 1/(k + 2)`; so `g ≤ 2 τ² + (k + 2) (2τ)^(2r)` for every `r ≥ 1`. Take
`p = ⌈k^δ⌉`. Then `E |g|^p ≤ B^p` with
`B = 4 C p (1/d + p/k²) + 2 (k + 2) 4^r (C r p (1/d + r p/k²))^r` by Lemma B.5
(`BDT24.LowDeg.overlapMoment_le`), and Hölder (`BDT24.SQ.avg_abs_le_of_moment`) gives an average
of `|g|` at most `q^(2/p) B ≤ 16 B` on every set of pairs of probability at least `1/q²`, for
`q = ⌈2^(k^δ)⌉ ≤ 2^(p+1)`. Under `n ≤ η min(d/k^δ, k^(2-2δ))`, `n p/d ≤ 2η` and `n p²/k² ≤ 4η`,
while the second term of `n B` is `O(k^(3 - r(1-δ)))`, small for `r = 5` and large `k`.
-/

@[expose] public section

namespace BDT24.SQ

namespace MS

open Matrix

/-- **The overlap of two spikes is at most `1`**: `⟨x_u, x_v⟩² ≤ 1`, by Cauchy–Schwarz, since the
spikes are unit vectors. -/
theorem spikeIP_sq_le_one_ms {d k : ℕ} {u v : Fin d → SignType} (hu : u ∈ spikeSigns d k)
    (hv : v ∈ spikeSigns d k) : LowDeg.spikeIP k u v ^ 2 ≤ 1 := by
  have hunit : ∀ w ∈ spikeSigns d k, spikeVector k w ⬝ᵥ spikeVector k w = 1 := by
    intro w hw
    rw [Prob.G.spikeVector_eq, smul_dotProduct, dotProduct_smul,
      Prob.G.spikeDir_dotProduct_self hw, smul_eq_mul, smul_eq_mul]
    have hs : √((k : ℝ) + 1) ^ 2 = k + 1 := Real.sq_sqrt (by positivity)
    have hs0 : √((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    rw [hs]
  have h := Prob.G.dotProduct_sq_le (spikeVector k u) (spikeVector k v)
  rw [hunit u hu, hunit v hv, one_mul] at h
  exact h

/-- **The gap of one correlation, pointwise**: `|⟨D̄_u, D̄_v⟩ - 1|^p` is at most
`2^(p-1) (2^p τ^(2p) + ((k + 2) 4^5)^p τ^(10p))` for the overlap `τ = ⟨x_u, x_v⟩`. -/
theorem gapPow_le_ms {d k p : ℕ} {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ ((k : ℝ) + 1) / ((k : ℝ) + 2)) {u v : Fin d → SignType} (hu : u ∈ spikeSigns d k)
    (hv : v ∈ spikeSigns d k) :
    |pairCorr k θ u v - 1| ^ p ≤ 2 ^ (p - 1) * (2 ^ p * LowDeg.spikeIP k u v ^ (2 * p) +
      (((k : ℝ) + 2) * 4 ^ 5) ^ p * LowDeg.spikeIP k u v ^ (2 * (5 * p))) := by
  have hθ1' : θ < 1 := lt_of_le_of_lt hθ1 (by rw [div_lt_one (by positivity)]; linarith)
  rw [pairCorr_eq hθ0.le hθ1' hu hv]
  set τ := LowDeg.spikeIP k u v
  obtain ⟨h0, h1⟩ := corrGap_quintic k hθ0.le hθ1 (sq_nonneg τ) (spikeIP_sq_le_one_ms hu hv)
  rw [abs_of_nonneg h0]
  calc (1 / √(1 - θ ^ 2 * τ ^ 2) - 1) ^ p ≤ (2 * τ ^ 2 + ((k : ℝ) + 2) * (4 * τ ^ 2) ^ 5) ^ p :=
        pow_le_pow_left₀ h0 h1 p
    _ ≤ 2 ^ (p - 1) * ((2 * τ ^ 2) ^ p + (((k : ℝ) + 2) * (4 * τ ^ 2) ^ 5) ^ p) :=
        add_pow_le (by positivity) (by positivity) p
    _ = _ := by
      have e : ((k : ℝ) + 2) * (4 * τ ^ 2) ^ 5 = ((k : ℝ) + 2) * 4 ^ 5 * τ ^ 10 := by ring
      rw [e, mul_pow _ (τ ^ 10), ← pow_mul]
      ring

/-- **The `p`-th moment of the gap**: `E |⟨D̄_u, D̄_v⟩ - 1|^p ≤ B^p` for two independent uniform
sign patterns, with `B = 4X + 2 (k + 2) 4^5 Y^5`, `X = C p (1/d + p/k²)` and
`Y = C (5p) (1/d + 5p/k²)`, given Lemma B.5 with the constant `C`. -/
theorem gapMoment_le_ms {d k p : ℕ} {θ C : ℝ}
    (hC : ∀ L : ℕ, 1 ≤ L →
      LowDeg.overlapMoment d k L ≤ (C * L) ^ L * (1 / (d : ℝ) + L / (k : ℝ) ^ 2) ^ L)
    (hC0 : 0 < C) (hp : 1 ≤ p) (hθ0 : 0 < θ) (hθ1 : θ ≤ ((k : ℝ) + 1) / ((k : ℝ) + 2)) :
    (∑ a ∈ spikeSigns d k ×ˢ spikeSigns d k, |pairCorr k θ a.1 a.2 - 1| ^ p) /
        ((spikeSigns d k ×ˢ spikeSigns d k).card : ℝ) ≤
      (4 * (C * p * (1 / (d : ℝ) + p / (k : ℝ) ^ 2)) + 2 * ((k : ℝ) + 2) * 4 ^ 5 *
        (C * (5 * p) * (1 / (d : ℝ) + 5 * p / (k : ℝ) ^ 2)) ^ 5) ^ p := by
  set S := spikeSigns d k
  set c : ℝ := ((k : ℝ) + 2) * 4 ^ 5
  set X : ℝ := C * p * (1 / (d : ℝ) + p / (k : ℝ) ^ 2)
  set Y : ℝ := C * (5 * p) * (1 / (d : ℝ) + 5 * p / (k : ℝ) ^ 2)
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  -- the pointwise bound, summed
  have hsum : ∑ a ∈ S ×ˢ S, |pairCorr k θ a.1 a.2 - 1| ^ p ≤
      ∑ a ∈ S ×ˢ S, 2 ^ (p - 1) * (2 ^ p * LowDeg.spikeIP k a.1 a.2 ^ (2 * p) +
        c ^ p * LowDeg.spikeIP k a.1 a.2 ^ (2 * (5 * p))) :=
    Finset.sum_le_sum fun a ha ↦ by
      rw [Finset.mem_product] at ha
      exact gapPow_le_ms hθ0 hθ1 ha.1 ha.2
  have heq : (∑ a ∈ S ×ˢ S, 2 ^ (p - 1) * (2 ^ p * LowDeg.spikeIP k a.1 a.2 ^ (2 * p) +
        c ^ p * LowDeg.spikeIP k a.1 a.2 ^ (2 * (5 * p)))) / ((S ×ˢ S).card : ℝ) =
      2 ^ (p - 1) * (2 ^ p * LowDeg.overlapMoment d k p +
        c ^ p * LowDeg.overlapMoment d k (5 * p)) := by
    unfold LowDeg.overlapMoment
    rw [Finset.card_product, Finset.sum_product]
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    push_cast
    ring
  have hm1 : LowDeg.overlapMoment d k p ≤ X ^ p := by
    have h := hC p hp
    rwa [← mul_pow] at h
  have hm2 : LowDeg.overlapMoment d k (5 * p) ≤ (Y ^ 5) ^ p := by
    have h := hC (5 * p) (by omega)
    rw [← mul_pow] at h
    push_cast at h
    rwa [← pow_mul]
  have hp0 : p ≠ 0 := by omega
  calc (∑ a ∈ S ×ˢ S, |pairCorr k θ a.1 a.2 - 1| ^ p) / ((S ×ˢ S).card : ℝ)
      ≤ (∑ a ∈ S ×ˢ S, 2 ^ (p - 1) * (2 ^ p * LowDeg.spikeIP k a.1 a.2 ^ (2 * p) +
        c ^ p * LowDeg.spikeIP k a.1 a.2 ^ (2 * (5 * p)))) / ((S ×ˢ S).card : ℝ) :=
        div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
    _ ≤ 2 ^ (p - 1) * (2 ^ p * X ^ p + c ^ p * (Y ^ 5) ^ p) := by
        rw [heq]
        gcongr
    _ = 2 ^ (p - 1) * ((2 * X) ^ p + (c * Y ^ 5) ^ p) := by
        rw [mul_pow (2 : ℝ) X p, mul_pow c (Y ^ 5) p]
    _ ≤ 2 ^ (p - 1) * (2 * X + c * Y ^ 5) ^ p := by
        gcongr
        exact pow_add_pow_le (by positivity) (by positivity) hp0
    _ ≤ 2 ^ p * (2 * X + c * Y ^ 5) ^ p := by
        gcongr
        · norm_num
        · omega
    _ = (4 * X + 2 * ((k : ℝ) + 2) * 4 ^ 5 * Y ^ 5) ^ p := by
        rw [← mul_pow]
        ring

end MS

/-- **Theorem C.6** of [BDT24]: the statement of `BDT24.sq_negSPCA`. -/
theorem sq_negSPCA_main :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 → ∃ η : ℝ, 0 < η ∧ ∃ k₀ : ℕ,
      ∀ n d k : ℕ, k₀ ≤ k → k ≤ d → 0 < n →
        (n : ℝ) ≤ η * min ((d : ℝ) / (k : ℝ) ^ δ) ((k : ℝ) ^ (2 - 2 * δ)) →
        ∀ θ : ℝ, 0 < θ → θ ≤ ((k : ℝ) + 1) / ((k : ℝ) + 2) →
          SDAAtLeast d k θ n ⌈(2 : ℝ) ^ ((k : ℝ) ^ δ)⌉₊ := by
  intro δ hδ hδ1
  obtain ⟨C, hC0, hC⟩ := LowDeg.overlapMoment_le
  have hη0 : 0 < 1 / (768 * C + 1) := by positivity
  refine ⟨1 / (768 * C + 1), hη0, ⌈2 * (98304 * (110 * C) ^ 5)⌉₊ + 1, ?_⟩
  intro n d k hk hkd hn hnb θ hθ0 hθ1 A hA hAS
  have hη1 : 1 / (768 * C + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hηC : 768 * C * (1 / (768 * C + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  set η := 1 / (768 * C + 1)
  have hk1 : 1 ≤ k := le_trans (Nat.le_add_left 1 _) hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := by linarith
  have hkK : 2 * (98304 * (110 * C) ^ 5) ≤ (k : ℝ) := by
    have h1 := Nat.le_ceil (2 * (98304 * (110 * C) ^ 5))
    have h2 : ((⌈2 * (98304 * (110 * C) ^ 5)⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at h2
    linarith
  -- `w = k^δ` and `p = ⌈w⌉`
  set w : ℝ := (k : ℝ) ^ δ with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow hkR hδ.le
  have hwk : w ≤ k := Real.rpow_le_self_of_one_le hkR (by linarith)
  have hw5 : w ^ 5 ≤ k := by
    rw [hw, ← Real.rpow_mul_natCast hk0.le]
    calc (k : ℝ) ^ (δ * ((5 : ℕ) : ℝ)) ≤ (k : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hkR (by push_cast; linarith)
      _ = k := Real.rpow_one _
  set p : ℕ := ⌈w⌉₊
  have hwp : w ≤ p := Nat.le_ceil w
  have hp2 : (p : ℝ) ≤ 2 * w := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ w)
    linarith
  have hp1 : 1 ≤ p := by
    have : (1 : ℝ) ≤ p := le_trans hw1 hwp
    exact_mod_cast this
  -- `q = ⌈2^w⌉ ≤ 2^(p+1)`
  set Q : ℕ := ⌈(2 : ℝ) ^ w⌉₊
  have hQp : (Q : ℝ) ≤ 2 ^ (p + 1) := by
    have h1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ (2 : ℝ) ^ w)
    have h2 : (2 : ℝ) ^ w ≤ 2 ^ p := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hwp
    have h3 : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith
  have hQ0 : (0 : ℝ) < Q := Nat.cast_pos.mpr (Nat.ceil_pos.mpr (by positivity))
  -- the bounds on `n`
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnd : (n : ℝ) * w ≤ η * d := by
    have h := hnb.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hη0.le)
    rw [mul_div_assoc', le_div_iff₀ (by linarith)] at h
    exact h
  have hnk : (n : ℝ) * w ^ 2 ≤ η * (k : ℝ) ^ 2 := by
    have h := hnb.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hη0.le)
    have e : (k : ℝ) ^ (2 - 2 * δ) = (k : ℝ) ^ 2 / w ^ 2 := by
      rw [Real.rpow_sub hk0, hw, ← Real.rpow_mul_natCast hk0.le, Real.rpow_two]
      push_cast
      ring_nf
    rw [e, mul_div_assoc', le_div_iff₀ (by positivity)] at h
    exact h
  -- Hölder with the moment bound
  have hAS' : 1 / (Q : ℝ) ^ 2 ≤
      (A.card : ℝ) / ((spikeSigns d k ×ˢ spikeSigns d k).card : ℝ) := by
    rw [Finset.card_product, Nat.cast_mul, ← sq]
    exact hAS
  have hH := avg_abs_le_of_moment hA (fun a ↦ pairCorr k θ a.1 a.2 - 1) hp1 hQ0 hAS'
    (MS.gapMoment_le_ms (fun L hL ↦ hC d k L hk1 hkd hL) hC0 hp1 hθ0 hθ1)
  refine hH.trans ((MS.rootSixteen_le hp1 hQ0.le hQp (by positivity)).trans ?_)
  exact MS.sixteenB_le_inv hC0 hη1 hηC hkR (by exact_mod_cast hkd) hnR hw1 hwk hw5
    (Nat.cast_nonneg p) hp2 hnd hnk hkK

end BDT24.SQ
