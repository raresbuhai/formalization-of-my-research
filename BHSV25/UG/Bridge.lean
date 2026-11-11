module

public import BHSV25.UG.Machine

/-!
# From the Unique Games Conjecture on graphs to left-regular instances

`BHSV25.UG.lrHard_of_khotUGC : UniqueGames.KhotUGC → BHSV25.BK.LRHard`, the instances that
Bansal and Khot's reduction starts from. For `ε ≤ 1/4`, take the conjecture at `ε / 4` and
`ℓ = ⌈2/ε⌉`:

1. the double cover (`BHSV25.UG.cover`) maps the gap `(1 - ε/4, ε/4)` on simple instances on
   graphs to the gap `(1 - ε/4, ε/2)` on bipartite instances with agreeing parallel constraints
   (`BHSV25.UG.cover_reduces`);
2. the regularization (`BHSV25.UG.regularize`) moves both thresholds by at most `1/ℓ ≤ ε/2`,
   onto the gap `(1 - ε, ε)` of left-regular instances with agreeing parallel constraints,
   `BHSV25.BK.lrGap` (`BHSV25.UG.regularize_reduces`).
-/

@[expose] public section

namespace BHSV25.UG

open UniqueGames BK Cslib.Complexity

/-- The gap problem on valid bipartite instances with `R` labels whose parallel constraints
agree. -/
noncomputable def bipGap (R : ℕ) (η ζ : ℝ) : PromiseProblem UGInstance :=
  (PromiseProblem.gapMax ugValue (fun _ ↦ 1 - η) (fun _ ↦ ζ)).restrict
    {G | UGValid G ∧ G.2.2.1 = R ∧ UGConsistent G}

/-- **The double cover** reduces the gap `(1 - η, ζ)` on graphs to `(1 - η, 2 ζ)`. -/
theorem cover_reduces (R : ℕ) {η ζ : ℝ} (hηζ : 2 * ζ < 1 - η) :
    PromiseProblem.PolyTimeReducible encUGGraph encUG (ugGraphGap R η ζ)
      (bipGap R η (2 * ζ)) := by
  refine ⟨cover, cover_polytime, ?_, ?_⟩
  · rintro G ⟨hyes, hv, hR, hs⟩
    exact ⟨le_trans hyes (ugGraphValue_le_cover hv), cover_valid hv, hR, cover_consistent hv hs⟩
  · rintro G ⟨⟨hno, -⟩, hv, hR, hs⟩
    have hn : ugGraphValue G ≤ ζ := hno
    refine ⟨⟨?_, hηζ⟩, cover_valid hv, hR, cover_consistent hv hs⟩
    change ugValue (cover G) ≤ 2 * ζ
    linarith [cover_le_two_mul hv]

/-- **The regularization** reduces the gap `(1 - η, ζ)` to `BHSV25.BK.lrGap R ε` when both
thresholds are within `ε` after moving by `1/ℓ`. -/
theorem regularize_reduces {R ℓ : ℕ} (hℓ : 1 ≤ ℓ) {η ζ ε : ℝ} (hη : η + 1 / ℓ ≤ ε)
    (hζ : ζ + 1 / ℓ ≤ ε) (hε : ε < 1 - ε) :
    PromiseProblem.PolyTimeReducible encUG encUG (bipGap R η ζ) (lrGap R ε) := by
  refine ⟨regularize ℓ, regularize_polytime ℓ, ?_, ?_⟩
  · rintro G ⟨hyes, hv, hR, hc⟩
    have hy : 1 - η ≤ ugValue G := hyes
    refine ⟨?_, regularize_good hv hR hc⟩
    change 1 - ε ≤ ugValue (regularize ℓ G)
    linarith [ugValue_le_regularize hℓ hv]
  · rintro G ⟨⟨hno, -⟩, hv, hR, hc⟩
    have hn : ugValue G ≤ ζ := hno
    refine ⟨⟨?_, hε⟩, regularize_good hv hR hc⟩
    change ugValue (regularize ℓ G) ≤ ε
    linarith [regularize_le_ugValue hℓ hv]

/-- **The bridge**: the Unique Games Conjecture on graphs gives the hardness of left-regular
instances that Bansal and Khot's reduction starts from. -/
theorem lrHard_of_khotUGC (h : KhotUGC) : LRHard := by
  obtain ⟨ε₀, hε₀, hK⟩ := h
  refine ⟨min (4 * ε₀) (1 / 4), lt_min (by positivity) (by norm_num),
    (min_le_right _ _).trans (by norm_num), fun ε hε hεle ↦ ?_⟩
  have hε4 : ε / 4 ≤ ε₀ := by linarith [min_le_left (4 * ε₀) (1 / 4)]
  have hε14 : ε ≤ 1 / 4 := hεle.trans (min_le_right _ _)
  obtain ⟨R, hR⟩ := hK (ε / 4) (by positivity) hε4
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℕ, ℓ = ⌈2 / ε⌉₊ := ⟨_, rfl⟩
  have hℓr : 2 / ε ≤ ℓ := hℓdef ▸ Nat.le_ceil _
  have hℓ1 : 1 ≤ ℓ := by
    have : (0 : ℝ) < ℓ := lt_of_lt_of_le (by positivity) hℓr
    exact_mod_cast this
  have hinv : 1 / (ℓ : ℝ) ≤ ε / 2 := by
    have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
    rw [div_le_iff₀ hℓ0]
    rw [div_le_iff₀ hε] at hℓr
    linarith
  exact ⟨R, (hR.trans (cover_reduces R (η := ε / 4) (ζ := ε / 4) (by linarith))).trans
    (regularize_reduces hℓ1 (by linarith) (by linarith) (by linarith))⟩

end BHSV25.UG
