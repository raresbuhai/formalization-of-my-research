module

public import BHSV25.Spectral.Basic
public import BHSV25.Net.Correct
public import BHSV25.Net.PolyTime

/-!
# Nets of eigenspaces, computed in polynomial time

The spectral algorithms of [BHSV25] enumerate a net of a low-dimensional eigenspace of the
normalized adjacency matrix `Ã` of the input graph (Lemmas 5.2 and 7.22). A Turing machine cannot
compute eigenvectors, so this file states what the algorithms use instead: for fixed rational
thresholds `0 < θ' < θ` and a fixed bound `T`, a polynomial-time map from a graph to a list of
rational vectors that contains, for every vector `w` of norm at most `1` in the span of the
eigenvectors of `Ã` with eigenvalue at most `-θ` (`BHSV25.Net.exists_bottomNet`), or at least `θ`
in absolute value (`BHSV25.Net.exists_absNet`), one within `κ / n` of `w`, on every regular graph
with at most `T` eigenvalues at most `-θ'` (respectively at least `θ'` in absolute value).

The input is the number of vertices and the adjacency table (the pair that `BHSV25.encGraph`
encodes), and a vector is a list of `n` rationals (`BHSV25.Net.vecOf`). The encodings are those of
`Background/Encoding.lean`, which agree with complexitylib's up to definitional unfolding.
-/

@[expose] public section

namespace BHSV25

namespace Net

open Turing.MultiTapeTM Matrix

/-- A list of rationals read as a real vector of length `n` (missing entries are `0`). -/
def vecOf (n : ℕ) (c : List ℚ) : Fin n → ℝ := fun i ↦ ((c.getD i 0 : ℚ) : ℝ)

/-- **Nets of the bottom eigenspace.** -/
theorem exists_bottomNet (θ' θ κ : ℚ) (hθ' : 0 < θ') (hθ : θ' < θ) (hθ1 : θ < 1) (hκ : 0 < κ)
    (T : ℕ) :
    ∃ net : ℕ × List Bool → List (List ℚ),
      ComputableInPolyTime net (Encoding.encPair Encoding.encNat Encoding.encBits)
        (Encoding.encList (Encoding.encList Encoding.encRat)) ∧
      ∀ G : Graph, G.IsRegular → (Finset.univ.filter fun i ↦ G.eig i ≤ -θ').card ≤ T →
        ∀ w : Fin G.1 → ℝ, w ⬝ᵥ w ≤ 1 → G.InEigSpan (· ≤ -θ) w →
          ∃ c ∈ net (G.1, adjTable G),
            (vecOf G.1 c - w) ⬝ᵥ (vecOf G.1 c - w) ≤ (κ / G.1) ^ 2 := by
  obtain ⟨p, hp⟩ := bottomNet_correct θ' θ κ hθ' hθ hθ1 hκ T
  exact ⟨netList p, netList_polytime p, hp⟩

/-- **Nets of the eigenspace of large eigenvalues in absolute value.** -/
theorem exists_absNet (θ' θ κ : ℚ) (hθ' : 0 < θ') (hθ : θ' < θ) (hθ1 : θ ≤ 1) (hκ : 0 < κ)
    (T : ℕ) :
    ∃ net : ℕ × List Bool → List (List ℚ),
      ComputableInPolyTime net (Encoding.encPair Encoding.encNat Encoding.encBits)
        (Encoding.encList (Encoding.encList Encoding.encRat)) ∧
      ∀ G : Graph, G.IsRegular → (Finset.univ.filter fun i ↦ θ' ≤ |G.eig i|).card ≤ T →
        ∀ w : Fin G.1 → ℝ, w ⬝ᵥ w ≤ 1 → G.InEigSpan (fun μ ↦ θ ≤ |μ|) w →
          ∃ c ∈ net (G.1, adjTable G),
            (vecOf G.1 c - w) ⬝ᵥ (vecOf G.1 c - w) ≤ (κ / G.1) ^ 2 := by
  obtain ⟨p, hp⟩ := absNet_correct θ' θ κ hθ' hθ hθ1 hκ T
  exact ⟨netList p, netList_polytime p, hp⟩

end Net

end BHSV25
