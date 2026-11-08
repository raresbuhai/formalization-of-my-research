module

public import BHJK25.RS.Decode.Elim
public import BHJK25.RS.Decode.Sudan
public import Mathlib.Data.List.GetD

/-!
# The per-guess decoder: the interpolant

Read in the field, the interpolant `BHJK25.RS.DecodeAux.interp` of at most `n` points, with
`m ≥ 2` and `W² > 2 n m`, is a nonzero `Q(X, Y)` with `X`-degrees at most `W`, `(1, m - 1)`-weighted
degree at most `W`, vanishing at every point (`BHJK25.RS.DecodeAux.Sem.interp_spec`): there are
more allowed monomials than points (`BHJK25.RS.Sudan.card_low`), so a nonzero allowed kernel
vector exists (`BHJK25.RS.Sudan.exists_kernel`), and the elimination finds one
(`BHJK25.RS.DecodeAux.Sem.kernelVec_spec`).
-/

@[expose] public section

namespace BHJK25.RS.DecodeAux

namespace Sem

open Polynomial

variable {fl : List ℕ} {F : Type*} [Field F] (S : Sem fl F)

/-- Reindexing `k = j N + i`. -/
private theorem sum_sum_eq_sum {M : Type*} [AddCommMonoid M] (B N : ℕ) (f : ℕ → M) :
    ∑ j ∈ Finset.range B, ∑ i ∈ Finset.range N, f (j * N + i) =
      ∑ k ∈ Finset.range (B * N), f k := by
  induction B with
  | zero => simp
  | succ B ih => rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]

/-- The value of `toBP` at a point. -/
theorem eval_map_toBP (BY L : ℕ) (Q : List (List (List ℕ))) (x y : F) :
    ((S.toBP BY L Q).map (evalRingHom x)).eval y =
      ∑ j ∈ Finset.range BY, ∑ i ∈ Finset.range L,
        S.ev ((Q.getD j []).getD i []) * x ^ i * y ^ j := by
  simp only [toBP, toP, Polynomial.map_sum, map_monomial, eval_finsetSum, eval_monomial,
    coe_evalRingHom, Finset.sum_mul]

/-- The entries of the interpolant. -/
theorem getD_interp (m W : ℕ) (pts : List (List ℕ × List ℕ)) (j i : ℕ) :
    ((interp fl m W pts).getD j []).getD i [] =
      if j < W + 1 ∧ i < W + 1 then
        (kernelVec fl ((W + 1) * (W + 1)) (initFam fl m W) (pts.map (row fl W))).getD
          (j * (W + 1) + i) []
      else [] := by
  simp only [interp, getD_map_range]
  by_cases hj : j < W + 1
  · by_cases hi : i < W + 1
    · rw [ite_eq_left hj, getD_map_range, ite_eq_left hi,
        ite_eq_left (show j < W + 1 ∧ i < W + 1 from ⟨hj, hi⟩)]
    · rw [ite_eq_left hj, getD_map_range, ite_eq_right hi, ite_eq_right fun h ↦ hi h.2]
  · rw [ite_eq_right hj, ite_eq_right fun h ↦ hj h.1, List.getD_nil]

/-- The coefficients of the interpolant. -/
theorem coeff_coeff_interp (m W : ℕ) {L : ℕ} (hL : W + 1 ≤ L) (pts : List (List ℕ × List ℕ))
    (j i : ℕ) : ((S.toBP (W + 1) L (interp fl m W pts)).coeff j).coeff i =
      if j < W + 1 ∧ i < W + 1 then
        S.ev ((kernelVec fl ((W + 1) * (W + 1)) (initFam fl m W) (pts.map (row fl W))).getD
          (j * (W + 1) + i) [])
      else 0 := by
  rw [coeff_coeff_toBP, getD_interp]
  by_cases h : j < W + 1 ∧ i < W + 1
  · rw [ite_eq_left (show j < W + 1 ∧ i < L from ⟨h.1, by omega⟩), ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    split_ifs <;> simp

/-- The entries of a row. -/
theorem ev_row (W : ℕ) (xy : List ℕ × List ℕ) {k : ℕ} (hk : k < (W + 1) * (W + 1)) :
    S.ev ((row fl W xy).getD k []) = S.ev xy.1 ^ (k % (W + 1)) * S.ev xy.2 ^ (k / (W + 1)) := by
  rw [row, getD_map_range, ite_eq_left hk, S.ev_mul, S.ev_pow, S.ev_pow]

/-- The elimination output is an allowed kernel vector. -/
private theorem kernelVec_interp {m W n : ℕ} (hm : 2 ≤ m) (hW : 2 * n * m < W * W)
    (pts : List (List ℕ × List ℕ)) (hpts : pts.length ≤ n) :
    let c := kernelVec fl ((W + 1) * (W + 1)) (initFam fl m W) (pts.map (row fl W))
    (∀ k < (W + 1) * (W + 1), low m W k = false → S.ev (c.getD k []) = 0) ∧
    (∃ k < (W + 1) * (W + 1), S.ev (c.getD k []) ≠ 0) ∧
    ∀ a ∈ pts.map (row fl W), ∑ k ∈ Finset.range ((W + 1) * (W + 1)), S.ev (a.getD k []) *
      S.ev (c.getD k []) = 0 := by
  refine S.kernelVec_spec m W _ ?_
  have hcard := Sudan.card_low hm hW
  have hset : ((Finset.range ((W + 1) * (W + 1))).filter
      fun k ↦ k % (W + 1) + (m - 1) * (k / (W + 1)) ≤ W) =
      (Finset.range ((W + 1) * (W + 1))).filter fun k ↦ low m W k = true :=
    Finset.filter_congr fun k _ ↦ by rw [low, decide_eq_true_iff]
  rw [hset] at hcard
  obtain ⟨v, hv1, hv2, hv3⟩ :=
    Sudan.exists_kernel (K := (W + 1) * (W + 1)) (fun k ↦ low m W k = true)
    ((pts.map (row fl W)).map fun a k ↦ S.ev (a.getD k []))
    (by rw [List.length_map, List.length_map]; omega)
  refine ⟨v, fun k hk hlow ↦ hv1 k hk (by rw [hlow]; exact Bool.false_ne_true), hv2,
    fun a ha ↦ hv3 _ (List.mem_map_of_mem ha)⟩

/-- **The interpolant.** For at most `n` points, `m ≥ 2` and `W² > 2 n m`, the interpolant is
nonzero, has `X`-degrees at most `W` and `(1, m - 1)`-weighted degree at most `W`, and vanishes at
every point. -/
theorem interp_spec {m W n : ℕ} (hm : 2 ≤ m) (hW : 2 * n * m < W * W) {L : ℕ}
    (hL : W + 1 ≤ L) (pts : List (List ℕ × List ℕ)) (hpts : pts.length ≤ n) :
    S.toBP (W + 1) L (interp fl m W pts) ≠ 0 ∧
      (∀ j, ((S.toBP (W + 1) L (interp fl m W pts)).coeff j).natDegree ≤ W) ∧
      (∀ b a, ((S.toBP (W + 1) L (interp fl m W pts)).coeff b).coeff a ≠ 0 →
        a + (m - 1) * b ≤ W) ∧
      ∀ xy ∈ pts,
        ((S.toBP (W + 1) L (interp fl m W pts)).map (evalRingHom (S.ev xy.1))).eval
          (S.ev xy.2) = 0 := by
  obtain ⟨hc1, ⟨k₀, hk₀, hc₀⟩, hc3⟩ := S.kernelVec_interp hm hW pts hpts
  set c := kernelVec fl ((W + 1) * (W + 1)) (initFam fl m W) (pts.map (row fl W))
  have hcoeff := S.coeff_coeff_interp m W hL pts
  have hW1 : 0 < W + 1 := Nat.succ_pos W
  refine ⟨fun h ↦ ?_, fun j ↦ ?_, fun b a hba ↦ ?_, fun xy hxy ↦ ?_⟩
  · -- the coefficient of `X^(k₀ % (W+1)) Y^(k₀ / (W+1))` is nonzero
    have h1 : k₀ / (W + 1) < W + 1 := Nat.div_lt_of_lt_mul hk₀
    have h2 : k₀ % (W + 1) < W + 1 := Nat.mod_lt _ hW1
    have h3 := hcoeff (k₀ / (W + 1)) (k₀ % (W + 1))
    rw [ite_eq_left (show _ ∧ _ from ⟨h1, h2⟩), Nat.div_add_mod', h, coeff_zero,
      coeff_zero] at h3
    exact hc₀ h3.symm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [hcoeff, ite_eq_right fun h ↦ by have := h.2; omega]
  · rw [hcoeff] at hba
    by_cases h : b < W + 1 ∧ a < W + 1
    · rw [ite_eq_left h] at hba
      have hk : b * (W + 1) + a < (W + 1) * (W + 1) := by
        have : (b + 1) * (W + 1) ≤ (W + 1) * (W + 1) := Nat.mul_le_mul_right _ h.1
        rw [Nat.succ_mul] at this
        omega
      have hlow : low m W (b * (W + 1) + a) = true := by
        by_contra hl
        exact hba (hc1 _ hk (by simpa using hl))
      have hmod : (b * (W + 1) + a) % (W + 1) = a := by
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt h.2]
      have hdiv : (b * (W + 1) + a) / (W + 1) = b := by
        rw [add_comm, Nat.add_mul_div_right _ _ hW1, Nat.div_eq_of_lt h.2, zero_add]
      rw [low, decide_eq_true_iff, hmod, hdiv] at hlow
      exact hlow
    · exact absurd (ite_eq_right h) hba
  · rw [eval_map_toBP]
    have hsplit : ∀ j ∈ Finset.range (W + 1),
        ∑ i ∈ Finset.range L, S.ev (((interp fl m W pts).getD j []).getD i []) *
          S.ev xy.1 ^ i * S.ev xy.2 ^ j =
        ∑ i ∈ Finset.range (W + 1), S.ev (c.getD (j * (W + 1) + i) []) *
          (S.ev xy.1 ^ ((j * (W + 1) + i) % (W + 1)) *
            S.ev xy.2 ^ ((j * (W + 1) + i) / (W + 1))) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [← Nat.add_sub_cancel' hL, Finset.sum_range_add]
      have hrest : ∑ i ∈ Finset.range (L - (W + 1)),
          S.ev (((interp fl m W pts).getD j []).getD (W + 1 + i) []) *
            S.ev xy.1 ^ (W + 1 + i) * S.ev xy.2 ^ j = 0 :=
        Finset.sum_eq_zero fun i _ ↦ by
          rw [getD_interp, ite_eq_right fun h ↦ by have := h.2; omega, S.ev_nil, zero_mul,
            zero_mul]
      rw [hrest, add_zero]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [Finset.mem_range] at hi
      have hmod : (j * (W + 1) + i) % (W + 1) = i := by
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hi]
      have hdiv : (j * (W + 1) + i) / (W + 1) = j := by
        rw [add_comm, Nat.add_mul_div_right _ _ hW1, Nat.div_eq_of_lt hi, zero_add]
      rw [getD_interp, ite_eq_left (show j < W + 1 ∧ i < W + 1 from ⟨hj, hi⟩), hmod, hdiv]
      ring
    rw [Finset.sum_congr rfl hsplit, sum_sum_eq_sum (W + 1) (W + 1)
      (fun k ↦ S.ev (c.getD k []) * (S.ev xy.1 ^ (k % (W + 1)) * S.ev xy.2 ^ (k / (W + 1))))]
    have h0 := hc3 (row fl W xy) (List.mem_map_of_mem hxy)
    rw [← h0]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [S.ev_row W xy (Finset.mem_range.mp hk), mul_comm]

end Sem

end BHJK25.RS.DecodeAux
