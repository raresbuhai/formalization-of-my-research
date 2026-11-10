module

public import BHSV25.Model
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Append
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Comp
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyZeroSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant

/-!
# Running times of a fixed degree

The algorithms of [BHSV25, Section 7] run in time `n^{O(1)} · g(p)` for parameters `p`
(`BHSV25.RunsInTime`, with the degree fixed before `p`). They are obtained here from one machine
`U` that reads the parameters together with the graph: `U` runs in polynomial time on the pair
`(p, a)`, proved with the closure rules of `Turing.MultiTapeTM.ComputableInPolyTime`, and fixing `p`
gives an algorithm running in time `c (|p| + 1)^C (m + 1)^C` on inputs of length `m`, where `c` and
`C` depend only on `U` (`BHSV25.runsInTime_fix`).

The degree `C` is that of the polynomial bounding `U`, so it does not depend on `p`, and the
factor `c (|p| + 1)^C` is explicit in the length of the encoded parameter. A parameter that
carries a unary padding of length `F` therefore gives the factor `O(F^C)`: this is how an
algorithm doing `F · poly(n)` work (a net of size `F` over the graph) gets its running time.

The fixed machine writes the framed parameter in front of its input and then runs `U`, with
complexitylib's tidy combinators for constant outputs, the identity, concatenation and
composition, whose time bounds are explicit.

* `BHSV25.runsInTime_fix`: fixing the parameter of a polynomial-time machine;
  `BHSV25.runsInTime_graph_fix` for algorithms reading a graph as `(n, a)`.
* `BHSV25.RunsInTime.mono`: larger factors and degrees.
-/

@[expose] public section

namespace BHSV25

open Turing.MultiTapeTM

/-- A frame doubles the length and adds one bit. -/
theorem length_frame (w : List Bool) : (Encoding.frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [Encoding.frame, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

/-- The arithmetic behind the factor of `BHSV25.runsInTime_fix`: linear terms in `L` and `m`,
and a power of `2 L + 2 + m`, are at most a multiple of `(L + 1)^(C+1) (m + 1)^(C+1)`. -/
theorem linear_add_pow_le (A B C L m : ℕ) :
    A * ((L + 1) * (m + 1)) + B * (2 * L + 2 + m) ^ C ≤
      (A + B) * 2 ^ (C + 1) * ((L + 1) ^ (C + 1) * (m + 1) ^ (C + 1)) := by
  have hL : 1 ≤ L + 1 := Nat.le_add_left 1 L
  have hm : 1 ≤ m + 1 := Nat.le_add_left 1 m
  have hP : (L + 1) * (m + 1) ≤ (L + 1) ^ (C + 1) * (m + 1) ^ (C + 1) :=
    Nat.mul_le_mul (Nat.le_self_pow (Nat.succ_ne_zero C) _) (Nat.le_self_pow (Nat.succ_ne_zero C) _)
  have hQ : (L + 1) ^ (C + 1) * (m + 1) ^ (C + 1) ≤
      2 ^ (C + 1) * ((L + 1) ^ (C + 1) * (m + 1) ^ (C + 1)) :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hbase : 2 * L + 2 + m ≤ 2 * ((L + 1) * (m + 1)) := by nlinarith
  have hpow : (2 * L + 2 + m) ^ C ≤ 2 ^ (C + 1) * ((L + 1) ^ (C + 1) * (m + 1) ^ (C + 1)) := by
    calc (2 * L + 2 + m) ^ C ≤ (2 * ((L + 1) * (m + 1))) ^ C := Nat.pow_le_pow_left hbase C
      _ = 2 ^ C * ((L + 1) ^ C * (m + 1) ^ C) := by rw [mul_pow, mul_pow]
      _ ≤ 2 ^ (C + 1) * ((L + 1) ^ (C + 1) * (m + 1) ^ (C + 1)) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right two_pos (Nat.le_succ C))
          (Nat.mul_le_mul (Nat.pow_le_pow_right hL (Nat.le_succ C))
            (Nat.pow_le_pow_right hm (Nat.le_succ C)))
  calc A * ((L + 1) * (m + 1)) + B * (2 * L + 2 + m) ^ C
      ≤ A * (2 ^ (C + 1) * ((L + 1) ^ (C + 1) * (m + 1) ^ (C + 1))) +
          B * (2 ^ (C + 1) * ((L + 1) ^ (C + 1) * (m + 1) ^ (C + 1))) :=
        Nat.add_le_add (Nat.mul_le_mul_left A (hP.trans hQ)) (Nat.mul_le_mul_left B hpow)
    _ = (A + B) * 2 ^ (C + 1) * ((L + 1) ^ (C + 1) * (m + 1) ^ (C + 1)) := by ring

/-- **Fixing the parameter of a polynomial-time machine.** If `U` is computable in polynomial time
on pairs `(p, a)`, then for every `p` the map `a ↦ U (p, a)` runs in time
`c (|p| + 1)^C · (m + 1)^C` on inputs of length `m`, with `c` and `C` independent of `p`. -/
theorem runsInTime_fix {P α β : Type} {encP : P ↪ List Bool} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {U : P × α → β}
    (hU : ComputableInPolyTime U (Encoding.encPair encP encIn) encOut) :
    ∃ c C : ℕ, ∀ p : P,
      RunsInTime (fun a ↦ U (p, a)) encIn encOut (c * ((encP p).length + 1) ^ C) C := by
  obtain ⟨tU, sU, htU, hsU, hTU⟩ := computableInPolyTime_iff_computableTidilyInPolyTime.mp hU
  obtain ⟨c₀, C₀, hc₀⟩ := htU.exists_le
  obtain ⟨c₁, C₁, hc₁⟩ := hsU.exists_le
  refine ⟨(25 + c₀) * 2 ^ (C₀ + 1), C₀ + 1, fun p ↦ ?_⟩
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
  obtain ⟨c₂, hcomp⟩ := hTU.comp hpre
  have hlen : ∀ a, (Encoding.encPair encP encIn (p, a)).length = 2 * L + 1 + (encIn a).length :=
    fun a ↦ by
      change (Encoding.frame (encP p) ++ encIn a).length = _
      rw [List.length_append, length_frame]
  have hwlen : w.length = 2 * L + 1 := length_frame _
  -- the space bound
  set S₀ := (k + c₂ + 10 + c₁) * 2 ^ (C₁ + 1) * (L + 1) ^ (C₁ + 1) with hS₀
  refine ⟨fun m ↦ S₀ * (m + 1) ^ (C₁ + 1),
    Cslib.PolynomiallyBounded.of_forall_le S₀ (C₁ + 1) (fun _ ↦ le_rfl), ?_⟩
  refine hcomp.computableInTimeAndSpace.mono (fun a ↦ ?_) (fun a ↦ ?_)
  · -- time
    set m := (encIn a).length with hm
    have htime : 2 * (2 + w.length) + 2 + (2 * m + 4) + tU (p, a) +
        4 * (Encoding.encPair encP encIn (p, a)).length + 9 ≤
        (25 + c₀) * 2 ^ (C₀ + 1) * ((L + 1) ^ (C₀ + 1) * (m + 1) ^ (C₀ + 1)) := by
      have h1 := hc₀ (p, a)
      rw [hlen] at h1 ⊢
      rw [hwlen]
      have h2 := linear_add_pow_le 25 c₀ C₀ L m
      have h3 : 2 * L + 1 + m + 1 = 2 * L + 2 + m := by omega
      rw [h3] at h1
      nlinarith
    have hreal : ((2 * (2 + w.length) + 2 + (2 * m + 4) + tU (p, a) +
        4 * (Encoding.encPair encP encIn (p, a)).length + 9 : ℕ) : ℝ) ≤
        (((25 + c₀) * 2 ^ (C₀ + 1) : ℕ) * ((L : ℝ) + 1) ^ (C₀ + 1)) * ((m : ℝ) + 1) ^ (C₀ + 1) := by
      have := (Nat.cast_le (α := ℝ)).mpr htime
      push_cast at this ⊢
      linarith
    exact Nat.cast_le.mp (hreal.trans (Nat.le_ceil _))
  · -- space
    set m := (encIn a).length with hm
    change 0 + 0 + k + sU (p, a) + 5 * (Encoding.encPair encP encIn (p, a)).length + c₂ ≤
      S₀ * (m + 1) ^ (C₁ + 1)
    have h1 := hc₁ (p, a)
    rw [hlen, ← hm] at h1 ⊢
    have h3 : 2 * L + 1 + m + 1 = 2 * L + 2 + m := by omega
    rw [h3] at h1
    have h2 := linear_add_pow_le (k + c₂ + 10) c₁ C₁ L m
    have h4 : S₀ * (m + 1) ^ (C₁ + 1) =
        (k + c₂ + 10 + c₁) * 2 ^ (C₁ + 1) * ((L + 1) ^ (C₁ + 1) * (m + 1) ^ (C₁ + 1)) := by
      rw [hS₀]; ring
    have hX : L + m + 1 ≤ (L + 1) * (m + 1) := by nlinarith
    have h5 : k + c₂ ≤ (k + c₂) * ((L + 1) * (m + 1)) :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have h6 : (k + c₂ + 10) * ((L + 1) * (m + 1)) =
        (k + c₂) * ((L + 1) * (m + 1)) + 10 * ((L + 1) * (m + 1)) := by ring
    rw [h4]
    linarith

/-- **Fixing the parameter, for graphs.** The algorithms read a graph as the pair `(n, a)` of its
number of vertices and its adjacency table, which `BHSV25.encGraph` encodes: if `V` is computable
in polynomial time on `(p, (n, a))`, then for every `p` the map `G ↦ V (p, (n, a))` runs in time
`c (|p| + 1)^C · (m + 1)^C` on graphs whose encoding has length `m`. -/
theorem runsInTime_graph_fix {P β : Type} {encP : P ↪ List Bool} {encOut : β ↪ List Bool}
    {V : P × (ℕ × List Bool) → β}
    (hV : ComputableInPolyTime V
      (Encoding.encPair encP (Encoding.encPair Encoding.encNat Encoding.encBits)) encOut) :
    ∃ c C : ℕ, ∀ p : P, RunsInTime (fun G : Graph ↦ V (p, (G.1, adjTable G))) encGraph encOut
      (c * ((encP p).length + 1) ^ C) C := by
  have he : ComputableInPolyTime (fun x : P × Graph ↦ (x.1, (x.2.1, adjTable x.2)))
      (Encoding.encPair encP encGraph)
      (Encoding.encPair encP (Encoding.encPair Encoding.encNat Encoding.encBits)) :=
    ComputableInPolyTime.of_eq fun _ ↦ rfl
  exact runsInTime_fix (hV.comp he)

/-- **Fixing the parameter, for graphs**, in the form of the statements. -/
theorem exists_runsInTime_graph_fix {P β : Type} {encP : P ↪ List Bool}
    {encOut : β ↪ List Bool} {V : P × (ℕ × List Bool) → β}
    (hV : ComputableInPolyTime V
      (Encoding.encPair encP (Encoding.encPair Encoding.encNat Encoding.encBits)) encOut) :
    ∃ C : ℕ, ∀ p : P, ∃ K : ℝ,
      RunsInTime (fun G : Graph ↦ V (p, (G.1, adjTable G))) encGraph encOut K C :=
  let ⟨_, C, h⟩ := runsInTime_graph_fix hV
  ⟨C, fun p ↦ ⟨_, h p⟩⟩

/-- Running times are monotone in the factor and, for a nonnegative factor, in the degree. -/
theorem RunsInTime.mono {α β : Type*} {A : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {K K' : ℝ} {C C' : ℕ} (h : RunsInTime A encIn encOut K C)
    (hK : K ≤ K') (hK' : 0 ≤ K') (hC : C ≤ C') : RunsInTime A encIn encOut K' C' := by
  obtain ⟨s, hs, h⟩ := h
  refine ⟨s, hs, h.mono (fun a ↦ Nat.ceil_mono ?_) (fun _ ↦ le_rfl)⟩
  have hm : (1 : ℝ) ≤ ((encIn a).length : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) (encIn a).length]
  calc K * (((encIn a).length : ℝ) + 1) ^ C ≤ K' * (((encIn a).length : ℝ) + 1) ^ C :=
        mul_le_mul_of_nonneg_right hK (by positivity)
    _ ≤ K' * (((encIn a).length : ℝ) + 1) ^ C' :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm hC) hK'

end BHSV25
