module

public import BMW26.Prob.Coins

/-!
# Spectral concentration: definitions

The facts about a weighted hypercube graph `w` (in practice the indicator weights `coinW a ω` of a
percolated hypercube `Q_m(p)`) from which [BMW26, Lemma 5.1] follows, in the form used here: the
error is a diagonal quadratic form (`BMW26.SpecClose`), see `BMW26/Spec/Deterministic.lean`.

* `BMW26.badSet w p γ`: the vertices whose degree is not within `γ p m` of `p m` (the paper's `R`).
* `BMW26.cutW w S T`: the weight of the edges between `S` and `T`.
* `BMW26.LowRel`: on functions of degree at most `r`, the energy of `w` is within `γ` of `p` times
  that of `Q_m` ([BMW26, Lemma 5.6]).
* `BMW26.LowSq`: on functions of degree at most `r`, `‖(L_w - p L) h‖² ≤ 4 p ⟨h, L h⟩`
  ([BMW26, Lemma 5.8]).
* `BMW26.GoodNorm`: on functions supported on the good vertices, the energies differ by at most
  `2 γ p m ‖h‖²` ([BMW26, Lemma 5.4]).
* `BMW26.BadLow`: functions of degree at most `r` put at most a `κ` fraction of their squared norm
  on the bad vertices ([BMW26, Lemma 5.9]).
* `BMW26.Disc`: the edge discrepancy between disjoint sets of good vertices
  ([BMW26, Lemma 5.3]).
-/

@[expose] public section

namespace BMW26

open Finset

variable {m : ℕ}

/-- The **bad vertices**: those whose degree is not within `γ p m` of its mean `p m`. -/
noncomputable def badSet (w : Fin m → Cube m → ℝ) (p γ : ℝ) : Finset (Cube m) := by
  classical
  exact univ.filter fun x ↦ γ * p * m < |deg w x - p * m|

open Classical in
/-- The weight of the edges between `S` and `T` (each edge `{x, flip x i}` with `xᵢ = false`
counted once, if one endpoint is in `S` and the other in `T`). -/
noncomputable def cutW (w : Fin m → Cube m → ℝ) (S T : Finset (Cube m)) : ℝ :=
  ∑ i, ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false),
    w i x * if (x ∈ S ∧ flip x i ∈ T) ∨ (x ∈ T ∧ flip x i ∈ S) then 1 else 0

/-- Relative spectral closeness on functions of degree at most `r`. -/
def LowRel (w : Fin m → Cube m → ℝ) (p γ : ℝ) (r : ℕ) : Prop :=
  ∀ g : Cube m → ℝ,
    |energy w (lowProj r g) - p * energy 1 (lowProj r g)| ≤ γ * p * energy 1 (lowProj r g)

/-- The squared error of `L_w - p L` on functions of degree at most `r`. -/
def LowSq (w : Fin m → Cube m → ℝ) (p : ℝ) (r : ℕ) : Prop :=
  ∀ g : Cube m → ℝ,
    ∑ x, lap (fun i y ↦ w i y - p) (lowProj r g) x ^ 2 ≤ 4 * p * energy 1 (lowProj r g)

/-- Spectral closeness on the good vertices: for `h` vanishing on the bad vertices,
`|energy w h - p energy 1 h| ≤ 2 γ p m ‖h‖²`. -/
def GoodNorm (w : Fin m → Cube m → ℝ) (p γ : ℝ) : Prop :=
  ∀ h : Cube m → ℝ, (∀ x ∈ badSet w p γ, h x = 0) →
    |energy w h - p * energy 1 h| ≤ 2 * γ * p * m * ∑ x, h x ^ 2

/-- Functions of degree at most `r` put at most `κ ‖g‖²` on the bad vertices. -/
def BadLow (w : Fin m → Cube m → ℝ) (p γ κ : ℝ) (r : ℕ) : Prop :=
  ∀ g : Cube m → ℝ, ∑ x ∈ badSet w p γ, lowProj r g x ^ 2 ≤ κ * ∑ x, g x ^ 2

/-- **Discrepancy** between disjoint sets of good vertices:
`|w(S, T) - p Q(S, T)| ≤ η p m √(|S| |T|)`. -/
def Disc (w : Fin m → Cube m → ℝ) (p γ η : ℝ) : Prop :=
  ∀ S T : Finset (Cube m), Disjoint S T → Disjoint S (badSet w p γ) → Disjoint T (badSet w p γ) →
    |cutW w S T - p * cutW 1 S T| ≤ η * p * m * Real.sqrt (S.card * T.card)

end BMW26
