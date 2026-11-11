module

public import BHSV25.Time
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds

/-!
# Running times with a padding

The algorithms of Theorems 7.12 and 7.20 enumerate a net whose size depends on the input, through
the number of rounds of the greedy selection, which the algorithm finds itself. As one machine for
all inputs they run in time `g(t) · n^{O(1)}` (`BHSV25.RunsInTimeWith`), where `t` bounds the
number of rounds. They are obtained from one machine `U` that reads, with the parameters and the
input, two unary paddings `2^F₁` and `2^F₂` for exponents `F₁, F₂` computed from the input in
polynomial time: the paddings pay for the enumeration, and `U` runs in polynomial time in the
length of everything it reads.

* `BHSV25.runsInTimeWith_fix_pad`: computing the paddings, writing the parameter and running `U`
  takes `c (|p| + 1)^C ((2^F₁ + 1) (2^F₂ + 1))^C · (m + 1)^C` steps on inputs of length `m`, where
  `c` and `C` depend only on `U`, `F₁` and `F₂`. The paddings are computed by doubling
  (complexitylib's `Turing.MultiTapeTM.ComputableInO.unary_two_pow`), within explicit bounds.
* `BHSV25.runsInTimeWith_graph_fix_pad`: the same for algorithms reading a graph as `(n, a)`.
-/

@[expose] public section

namespace BHSV25

open Turing.MultiTapeTM

/-- Powers of numbers at most `Π`, for `Π ≥ 1`, are at most `Π^D` for exponents at most `D`. -/
theorem pow_le_pow_of_le {x P k D : ℕ} (hx : x ≤ P) (hP : 1 ≤ P) (hk : k ≤ D) :
    x ^ k ≤ P ^ D :=
  (Nat.pow_le_pow_left hx k).trans (Nat.pow_le_pow_right hP hk)

/-- `(n + 1) 2^n ≤ (2^n + 1)^2`. -/
theorem succ_mul_two_pow_le (n : ℕ) : (n + 1) * 2 ^ n ≤ (2 ^ n + 1) ^ 2 := by
  have h : n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ (Nat.lt_two_pow_self).le
  nlinarith

/-- The arithmetic of `BHSV25.runsInTimeWith_fix_pad`. -/
theorem pad_time_le (cW d₀ d₁ d₂ L m F₁ F₂ : ℕ) :
    2 * (2 + (2 * L + 1)) + 2 + (2 * m + 4) +
        cW * ((2 * L + 1 + m) + (((2 * L + 1 + m) + 1) ^ d₁ + (F₁ + 1) * 2 ^ F₁ +
          (((2 * L + 1 + m) + 1) ^ d₂ + (F₂ + 1) * 2 ^ F₂) + (2 * L + 1 + m)) +
          (2 * L + 4 * 2 ^ F₁ + 2 * 2 ^ F₂ + m + 4 + 1) ^ d₀ + 1) +
        4 * (2 * L + 1 + m) + 9 ≤
      (43 + cW * (8 * 9 ^ (d₀ + d₁ + d₂ + 2))) *
        ((L + 1) ^ (d₀ + d₁ + d₂ + 2) * (m + 1) ^ (d₀ + d₁ + d₂ + 2) *
          ((2 ^ F₁ + 1) * (2 ^ F₂ + 1)) ^ (d₀ + d₁ + d₂ + 2)) := by
  set D := d₀ + d₁ + d₂ + 2 with hD
  set P1 := 2 ^ F₁ with hP1
  set P2 := 2 ^ F₂ with hP2
  set R := (L + 1) * (m + 1) * ((P1 + 1) * (P2 + 1)) with hR
  have hp1 : 1 ≤ P1 + 1 := Nat.le_add_left 1 _
  have hp2 : 1 ≤ P2 + 1 := Nat.le_add_left 1 _
  have hl1 : 1 ≤ L + 1 := Nat.le_add_left 1 _
  have hm1 : 1 ≤ m + 1 := Nat.le_add_left 1 _
  have hpp : 1 ≤ (P1 + 1) * (P2 + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hL : L + 1 ≤ R := by
    rw [hR, mul_assoc]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have hm : m + 1 ≤ R := by
    rw [hR, mul_comm (L + 1), mul_assoc]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have hP1R : P1 + 1 ≤ R := by
    have : P1 + 1 ≤ (P1 + 1) * (P2 + 1) := Nat.le_mul_of_pos_right _ (by positivity)
    exact this.trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hP2R : P2 + 1 ≤ R := by
    have : P2 + 1 ≤ (P1 + 1) * (P2 + 1) := Nat.le_mul_of_pos_left _ (by positivity)
    exact this.trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hR1 : 1 ≤ R := hl1.trans hL
  set Q := 9 * R with hQ
  have hQ1 : 1 ≤ Q := by omega
  have hX : 2 * L + 1 + m + 1 ≤ Q := by omega
  have hY : 2 * L + 4 * P1 + 2 * P2 + m + 4 + 1 ≤ Q := by omega
  have hF1 : (F₁ + 1) * P1 ≤ Q ^ D := by
    refine (succ_mul_two_pow_le F₁).trans (pow_le_pow_of_le (by omega) hQ1 (by omega))
  have hF2 : (F₂ + 1) * P2 ≤ Q ^ D := by
    refine (succ_mul_two_pow_le F₂).trans (pow_le_pow_of_le (by omega) hQ1 (by omega))
  have hX1 : (2 * L + 1 + m + 1) ^ d₁ ≤ Q ^ D := pow_le_pow_of_le hX hQ1 (by omega)
  have hX2 : (2 * L + 1 + m + 1) ^ d₂ ≤ Q ^ D := pow_le_pow_of_le hX hQ1 (by omega)
  have hY0 : (2 * L + 4 * P1 + 2 * P2 + m + 4 + 1) ^ d₀ ≤ Q ^ D :=
    pow_le_pow_of_le hY hQ1 (by omega)
  have hXl : 2 * L + 1 + m ≤ Q ^ D :=
    (Nat.le_of_succ_le hX).trans (Nat.le_self_pow (by omega) Q)
  have hT : (2 * L + 1 + m) + ((2 * L + 1 + m + 1) ^ d₁ + (F₁ + 1) * P1 +
      ((2 * L + 1 + m + 1) ^ d₂ + (F₂ + 1) * P2) + (2 * L + 1 + m)) +
      (2 * L + 4 * P1 + 2 * P2 + m + 4 + 1) ^ d₀ + 1 ≤ 8 * Q ^ D := by
    have : 1 ≤ Q ^ D := Nat.one_le_pow _ _ hQ1
    omega
  have hQD : Q ^ D = 9 ^ D * R ^ D := by rw [hQ, mul_pow]
  have hlin : 2 * (2 + (2 * L + 1)) + 2 + (2 * m + 4) + 4 * (2 * L + 1 + m) + 9 ≤ 43 * R ^ D := by
    have : R ≤ R ^ D := Nat.le_self_pow (by omega) R
    omega
  have hRD : R ^ D = (L + 1) ^ D * (m + 1) ^ D * ((P1 + 1) * (P2 + 1)) ^ D := by
    rw [hR, mul_pow, mul_pow]
  rw [← hRD]
  have h2 := Nat.mul_le_mul_left cW hT
  rw [hQD] at h2
  nlinarith

/-- **Fixing the parameter, with paddings.** If `U` is computable in polynomial time on
`(p, ((P₁, P₂), a))`, with `P₁` and `P₂` in unary, and `F₁` and `F₂` are computable in polynomial
time on `(p, a)`, then for every `p` the map `a ↦ U (p, ((2^F₁(p, a), 2^F₂(p, a)), a))` runs in
time `c (|p| + 1)^C ((2^F₁ + 1) (2^F₂ + 1))^C · (m + 1)^C` on inputs of length `m`, with `c` and
`C` independent of `p`. -/
theorem runsInTimeWith_fix_pad {P α β : Type} {encP : P ↪ List Bool} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {U : P × ((ℕ × ℕ) × α) → β}
    (hU : ComputableInPolyTime U
      (Encoding.encPair encP (Encoding.encPair (Encoding.encPair encUnary encUnary) encIn)) encOut)
    {F₁ F₂ : P × α → ℕ}
    (hF₁ : ComputableInPolyTime F₁ (Encoding.encPair encP encIn) encUnary)
    (hF₂ : ComputableInPolyTime F₂ (Encoding.encPair encP encIn) encUnary) :
    ∃ c C : ℕ, ∀ p : P,
      RunsInTimeWith (fun a ↦ U (p, ((2 ^ F₁ (p, a), 2 ^ F₂ (p, a)), a))) encIn encOut
        (fun a ↦ (c : ℝ) * ((encP p).length + 1) ^ C *
          (((2 ^ F₁ (p, a) + 1) * (2 ^ F₂ (p, a) + 1) : ℕ) : ℝ) ^ C) C := by
  obtain ⟨d₁, e₁, h₁⟩ := hF₁.exists_degree
  obtain ⟨d₂, e₂, h₂⟩ := hF₂.exists_degree
  obtain ⟨d₀, e₀, h₀⟩ := hU.exists_degree
  -- the machine on `(p, a)`: the paddings by doubling, then `U`
  have hp1 := ComputableInO.unary_two_pow.tidy.comp h₁.inO.tidy
  have hp2 := ComputableInO.unary_two_pow.tidy.comp h₂.inO.tidy
  have hall := (ComputableTidilyInO.fst encP encIn).prod
    ((hp1.prod hp2).prod (ComputableTidilyInO.snd encP encIn))
  obtain ⟨cW, hWt, -⟩ := h₀.inO.tidy.comp hall
  refine ⟨43 + cW * (8 * 9 ^ (d₀ + d₁ + d₂ + 2)), d₀ + d₁ + d₂ + 2, fun p ↦ ?_⟩
  set w := Encoding.frame (encP p) with hw
  set L := (encP p).length with hL
  -- the machine writing `w` in front of its input
  have hconst : ComputableInTimeAndSpace (Function.const α w) encIn Encoding.encBits
      (fun _ ↦ 2 + w.length) (fun _ ↦ 0) := by
    have h := computableInTimeAndSpace_almostConstTime (encIn := encIn)
      (encOut := Encoding.encBits) (Function.const α w) ∅ w (fun _ _ ↦ rfl)
    simpa [almostConstTime] using h
  obtain ⟨k, hpre⟩ := hconst.computableTidilyInTimeAndSpace.append
    (computableTidilyInTimeAndSpace_id (enc := encIn)) (g := fun a ↦ (p, a))
    (encOut := Encoding.encPair encP encIn) (fun _ ↦ rfl)
  obtain ⟨c₂, hcomp⟩ := hWt.comp hpre
  unfold RunsInTimeWith
  refine ⟨_, hcomp.computableInTimeAndSpace.mono (s' := fun a ↦ _) (fun a ↦ ?_) (fun _ ↦ le_rfl)⟩
  set m := (encIn a).length with hm
  have hwlen : w.length = 2 * L + 1 := length_frame _
  have hX : (Encoding.encPair encP encIn (p, a)).length = 2 * L + 1 + m := by
    change (Encoding.frame (encP p) ++ encIn a).length = _
    rw [List.length_append, length_frame]
  have hY : (Encoding.encPair encP (Encoding.encPair (Encoding.encPair encUnary encUnary) encIn)
      (p, ((2 ^ F₁ (p, a), 2 ^ F₂ (p, a)), a))).length =
      2 * L + 4 * 2 ^ F₁ (p, a) + 2 * 2 ^ F₂ (p, a) + m + 4 := by
    change (Encoding.frame (encP p) ++ (Encoding.frame (Encoding.frame (encUnary (2 ^ F₁ (p, a))) ++
      encUnary (2 ^ F₂ (p, a))) ++ encIn a)).length = _
    simp only [List.length_append, length_frame, encUnary_apply, List.length_replicate]
    omega
  have key := pad_time_le cW d₀ d₁ d₂ L m (F₁ (p, a)) (F₂ (p, a))
  have hnat : 2 * (2 + w.length) + 2 + (2 * m + 4) +
      cW * ((Encoding.encPair encP encIn (p, a)).length +
        (((Encoding.encPair encP encIn (p, a)).length + 1) ^ d₁ + (F₁ (p, a) + 1) * 2 ^ F₁ (p, a) +
          (((Encoding.encPair encP encIn (p, a)).length + 1) ^ d₂ +
            (F₂ (p, a) + 1) * 2 ^ F₂ (p, a)) + (Encoding.encPair encP encIn (p, a)).length) +
        ((Encoding.encPair encP (Encoding.encPair (Encoding.encPair encUnary encUnary) encIn)
          (p, ((2 ^ F₁ (p, a), 2 ^ F₂ (p, a)), a))).length + 1) ^ d₀ + 1) +
      4 * (Encoding.encPair encP encIn (p, a)).length + 9 ≤
      (43 + cW * (8 * 9 ^ (d₀ + d₁ + d₂ + 2))) *
        ((L + 1) ^ (d₀ + d₁ + d₂ + 2) * (m + 1) ^ (d₀ + d₁ + d₂ + 2) *
          ((2 ^ F₁ (p, a) + 1) * (2 ^ F₂ (p, a) + 1)) ^ (d₀ + d₁ + d₂ + 2)) := by
    rw [hwlen, hX, hY]
    exact key
  refine le_trans hnat (Nat.cast_le.mp (le_trans (le_of_eq ?_) (Nat.le_ceil _)))
  push_cast
  ring

/-- **Fixing the parameter, with paddings, for graphs**: `BHSV25.runsInTimeWith_fix_pad` for
algorithms reading a graph as the pair `(n, a)` of its number of vertices and its adjacency
table. -/
theorem runsInTimeWith_graph_fix_pad {P β : Type} {encP : P ↪ List Bool}
    {encOut : β ↪ List Bool} {V : P × ((ℕ × ℕ) × (ℕ × List Bool)) → β}
    (hV : ComputableInPolyTime V (Encoding.encPair encP (Encoding.encPair
      (Encoding.encPair encUnary encUnary) (Encoding.encPair Encoding.encNat Encoding.encBits)))
      encOut)
    {F₁ F₂ : P × (ℕ × List Bool) → ℕ}
    (hF₁ : ComputableInPolyTime F₁
      (Encoding.encPair encP (Encoding.encPair Encoding.encNat Encoding.encBits)) encUnary)
    (hF₂ : ComputableInPolyTime F₂
      (Encoding.encPair encP (Encoding.encPair Encoding.encNat Encoding.encBits)) encUnary) :
    ∃ c C : ℕ, ∀ p : P,
      RunsInTimeWith (fun G : Graph ↦ V (p, ((2 ^ F₁ (p, (G.1, adjTable G)),
          2 ^ F₂ (p, (G.1, adjTable G))), (G.1, adjTable G)))) encGraph encOut
        (fun G ↦ (c : ℝ) * ((encP p).length + 1) ^ C *
          (((2 ^ F₁ (p, (G.1, adjTable G)) + 1) * (2 ^ F₂ (p, (G.1, adjTable G)) + 1) : ℕ) :
            ℝ) ^ C) C := by
  have he : ComputableInPolyTime
      (fun z : P × ((ℕ × ℕ) × Graph) ↦ (z.1, (z.2.1, (z.2.2.1, adjTable z.2.2))))
      (Encoding.encPair encP (Encoding.encPair (Encoding.encPair encUnary encUnary) encGraph))
      (Encoding.encPair encP (Encoding.encPair (Encoding.encPair encUnary encUnary)
        (Encoding.encPair Encoding.encNat Encoding.encBits))) :=
    ComputableInPolyTime.of_eq fun _ ↦ rfl
  have he' : ComputableInPolyTime (fun z : P × Graph ↦ (z.1, (z.2.1, adjTable z.2)))
      (Encoding.encPair encP encGraph)
      (Encoding.encPair encP (Encoding.encPair Encoding.encNat Encoding.encBits)) :=
    ComputableInPolyTime.of_eq fun _ ↦ rfl
  exact runsInTimeWith_fix_pad (hV.comp he) (hF₁.comp he') (hF₂.comp he')

end BHSV25
