module

public import ABBKS26.Rounding.Nested

/-!
# Gram factors of sums of squares

A sum of squares of bounded degree has a Gram factor on the full list of monomials; this is
how a nested sum-of-squares proof becomes variables of the outer program in [ABBKS26,
Lemma 4.3].
-/

@[expose] public section

namespace ABBKS26.Gram

noncomputable section


open Matrix

open Common MvPolynomial
open scoped BigOperators
variable {d : ℕ}

def gridConst (d e : ℕ) : ℕ :=
  (d + 1) ^ e * SoS.interpBound e ^ (2 * d) * (e + 1) ^ d


private theorem monos_nodup (d e : ℕ) : (Rounding.monos d e).Nodup := by
  exact (SoS.Mono.nodup_all d e).map_on fun a ha b hb h ↦
    SoS.Mono.toFinsupp_inj (SoS.Mono.mem_all.1 ha).1 (SoS.Mono.mem_all.1 hb).1 h

private theorem mem_monos {e : ℕ} {μ : Fin d →₀ ℕ} :
    μ ∈ Rounding.monos d e ↔ μ.degree ≤ e := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
    exact (SoS.Mono.degree_toFinsupp (SoS.Mono.mem_all.1 ha).1).trans_le
      (SoS.Mono.mem_all.1 ha).2
  · intro h
    let a := List.ofFn fun i : Fin d ↦ μ i
    have ha : a.length = d := by simp [a]
    have he : SoS.Mono.toFinsupp d a = μ := by
      ext i
      simp [SoS.Mono.toFinsupp_apply, a]
    have hs : a.sum ≤ e := by
      rw [← SoS.Mono.degree_toFinsupp ha, he]
      exact h
    exact List.mem_map.2 ⟨a, SoS.Mono.mem_all.2 ⟨ha, hs⟩, he⟩

private theorem gridPoint_eq {e : ℕ} (x : Fin d → Fin (e + 1)) :
    SoS.gridPoint x = fun i ↦ (x i : ℝ) := rfl

/-- A bounded-degree sum of squares has a factor on the full monomial list. -/
theorem gram_factor
    (p : RPoly d) (e : ℕ) (hp : IsSumSq p) (hd : p.totalDegree ≤ 2 * e) :
    let L := Rounding.monos d e
    ∃ G : Matrix (Fin L.length) (Fin L.length) ℝ,
      p = ∑ c, (∑ a, C (G a c) * monomial L[a] 1) ^ 2 ∧
      (∑ a, ∑ c, G a c ^ 2) ≤
        gridConst d e * ∑ x : Fin d → Fin (e + 1), eval (fun i ↦ (x i : ℝ)) p := by
  simpa only [gridConst, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    gridPoint_eq] using
    Rounding.NestedAux.boundedGram (Rounding.monos d e) (monos_nodup d e)
      (fun μ ↦ mem_monos) p hp hd


end

end ABBKS26.Gram
