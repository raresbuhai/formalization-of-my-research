module

public import BCFGJPSSV26.FL.Run
public import BCFGJPSSV26.FL.PolyTime

/-!
# Theorem 1.4

[BCFGJPSSV26a, Theorem 1.4] (Theorem 4.3 in full): `BCFGJPSSV26.FL.fl_main` proves the statement
`BCFGJPSSV26.FL.Thm14` of `BCFGJPSSV26.facilityLocation_lmp`, a polynomial-time `1.9499`-LMP
algorithm for uncapacitated facility location. The algorithm is `BCFGJPSSV26.FL.alg` on the tuple of
the instance and the opening cost (`FL/Algorithm.lean`): the greedy algorithm of [BCFGJPSSV26a,
Section 5], with exact tests, run once by CompleteSolution on a scaled instance, or the trivial
solution, whichever has the smaller objective `cost S + 1.9499 f |S|`. It runs in polynomial time
(`BCFGJPSSV26.FL.alg_polytime`) and satisfies the guarantee (`BCFGJPSSV26.FL.alg_spec`).

The proof of the guarantee (`BCFGJPSSV26.FL.alg_spec`), for an optimal set `O`
(`BCFGJPSSV26.FL.exists_optFL`):

* if the trivial solution has at most `|O|` facilities, or `f = 0`, it meets the bound
  (`BCFGJPSSV26.FL.score_trivialSol_le`);
* otherwise `n ≥ 2`, `m ≥ 2`, `f > 0`, and `O` has a positive cost
  (`BCFGJPSSV26.FL.trivialSol_length_le_card`), so the greedy run meets the bound
  (`BCFGJPSSV26.FL.runFL_spec`, from the robust LMP guarantee
  `BCFGJPSSV26.Greedy.robust_lmp` of Theorem 1.2's analysis);
* the output has the smaller objective of the two (`BCFGJPSSV26.FL.alg_spec_of`).
-/

@[expose] public section

namespace BCFGJPSSV26.FL

open Encoding

variable {I : Instance}

open Greedy in
/-- **The guarantee of the algorithm**: on a valid instance with a client and an opening cost
`f ≥ 0`, a nonempty list of distinct facilities `S` with `cost S ≤ 1.9499 (OPT_f - f |S|)`. -/
theorem alg_spec (hI : I.Valid) (hn : 0 < I.n) {f : ℚ} (hf : 0 ≤ f) :
    I.IsCenterList (alg (toRaw I) f) ∧
      I.cost (I.centers (alg (toRaw I) f)) ≤
        1.9499 * (I.optFL (f : ℝ) - (f : ℝ) * (alg (toRaw I) f).length) := by
  obtain ⟨O, hO, hopt⟩ := exists_optFL hI (f : ℝ)
  have hcase : (score (toRaw I) f (trivialSol (toRaw I)) : ℝ) ≤ (lmpC : ℝ) * I.optFL f ∨
      (I.IsCenterList (runFL (toRaw I) f) ∧
        (score (toRaw I) f (runFL (toRaw I) f) : ℝ) ≤ (lmpC : ℝ) * I.optFL f) := by
    by_cases hT : (trivialSol (toRaw I)).length ≤ O.card ∨ f = 0
    · exact .inl (score_trivialSol_le hI hn hf hO hopt hT)
    · push Not at hT
      obtain ⟨hTO, hf0⟩ := hT
      have hO1 : 1 ≤ O.card := Finset.card_pos.2 hO
      have hn2 : 2 ≤ I.n := by
        have := trivialSol_length_le_n (I := I)
        omega
      have hm2 : 2 ≤ I.m := by
        have := trivialSol_length_le_m hI
        omega
      have hc : 0 < I.cost O := lt_of_le_of_ne (Instance.cost_nonneg' hI O) fun h ↦
        absurd (trivialSol_length_le_card hI hO h.symm) (not_le.2 hTO)
      have hfpos : 0 < f := lt_of_le_of_ne hf (Ne.symm hf0)
      obtain ⟨h1, h2⟩ := runFL_spec hI hn2 hm2 hfpos hO hc
      exact .inr ⟨h1, by rw [hopt]; exact h2⟩
  have h := alg_spec_of hI hn f hcase
  exact ⟨h.1, lmp_of_score h.1 h.2⟩

/-- The statement of **Theorem 1.4** (`BCFGJPSSV26.facilityLocation_lmp`). -/
def Thm14 : Prop :=
    ∃ A : Instance × ℚ → List ℕ,
      Turing.MultiTapeTM.ComputableInPolyTime A (encPair encInstance encRat) encCenters ∧
      ∀ I : Instance, I.Valid → 0 < I.n → ∀ f : ℚ, 0 ≤ f →
        I.IsCenterList (A (I, f)) ∧
        I.cost (I.centers (A (I, f))) ≤
          1.9499 * (I.optFL (f : ℝ) - (f : ℝ) * (A (I, f)).length)

/-- **Theorem 1.4** of [BCFGJPSSV26a]: the statement of `BCFGJPSSV26.facilityLocation_lmp`. -/
theorem fl_main : Thm14 :=
  ⟨fun p ↦ alg (toRaw p.1) p.2, alg_polytime, fun _ hI hn _ hf ↦ alg_spec hI hn hf⟩

end BCFGJPSSV26.FL
