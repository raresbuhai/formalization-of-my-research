module

public import BGHKLMM26.Hardness.Decoder
public import BGHKLMM26.Hardness.TwoSided
public import Complexity.Probability.PMF.Uniform

/-!
# The coins of the reduction

The reduction reads its coins in consecutive blocks, one per sampled edge, so the probability of
an event about its output is the fraction of tuples of independent blocks on which it holds
(`BGHKLMM26.Hard.prob_reduce`).
-/

@[expose] public section

namespace BGHKLMM26.Hard

open UniqueGames

open Finset Cslib Cslib.Probability

variable {P : Prm} {G : UGInstance}

theorem coinCount_eq (hok : P.ok G = true) : P.coinCount G = P.samples G * P.blockLen G := by
  simp [Prm.coinCount, hok]

theorem range_map_eq_ofFn {α : Type*} (S : ℕ) (g : ℕ → α) :
    (List.range S).map g = List.ofFn fun i : Fin S ↦ g i := by
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

/-- The output of the reduction is the sampled graph of the blocks of its coins. -/
theorem reduce_blocks (hG : GoodI P.R G) (hok : P.ok G = true)
    (w : Fin (P.samples G * P.blockLen G) → Bool) :
    reduce P (G, List.ofFn w) =
      sampledGraph (P.nVert G) P.Δ (dec hG hok) (BitString.block w) := by
  simp only [reduce, hok, ite_true, sampledGraph]
  congr 2
  rw [range_map_eq_ofFn]
  congr 1
  funext i
  change edgeOfBlock P G (BitString.listBlock (P.blockLen G) (List.ofFn w) i) =
    ((dec hG hok (BitString.block w i)).1.val, (dec hG hok (BitString.block w i)).2.val)
  rw [BitString.listBlock_ofFn]
  rfl

/-- **The probability of an event about the output** is the fraction of the tuples of blocks
where it holds. -/
theorem prob_reduce (hG : GoodI P.R G) (hok : P.ok G = true) (Y : Set Graph) :
    ((ProbComp.eval ((fun w ↦ reduce P (G, w)) <$>
        BitString.sampleList (P.coinCount G))).toOuterMeasure Y).toReal =
      frac (fun ω : Fin (P.samples G) → (Fin (P.blockLen G) → Bool) ↦
        sampledGraph (P.nVert G) P.Δ (dec hG hok) ω ∈ Y) := by
  classical
  rw [coinCount_eq hok, ProbComp.eval_map, BitString.eval_sampleList, BitString.uniformList,
    PMF.map_comp, PMF.toOuterMeasure_map_apply,
    Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal]
  unfold frac
  have hcard : (Fintype.card (Fin (P.samples G * P.blockLen G) → Bool) : ℝ) =
      Fintype.card (Fin (P.samples G) → Fin (P.blockLen G) → Bool) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast
    rw [← pow_mul, mul_comm]
  rw [hcard]
  congr 1
  have : ((univ.filter fun w : Fin (P.samples G * P.blockLen G) → Bool ↦
      w ∈ (fun w ↦ reduce P (G, w)) ∘ List.ofFn ⁻¹' Y).card) =
      (univ.filter fun ω : Fin (P.samples G) → (Fin (P.blockLen G) → Bool) ↦
        sampledGraph (P.nVert G) P.Δ (dec hG hok) ω ∈ Y).card := by
    refine Finset.card_bij (fun w _ ↦ BitString.block w) (fun w hw ↦ ?_) (fun w _ w' _ h ↦ ?_)
      (fun ω hω ↦ ?_)
    · simp only [mem_filter, mem_univ, true_and, Set.mem_preimage, Function.comp_apply] at hw ⊢
      rwa [← reduce_blocks hG hok]
    · exact (BitString.blocksEquiv (α := Bool)).injective h
    · refine ⟨BitString.blocksEquiv.symm ω, ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and, Set.mem_preimage, Function.comp_apply]
        rw [reduce_blocks hG hok, BitString.block_blocksEquiv_symm]
        simpa using hω
      · exact BitString.block_blocksEquiv_symm ω
  exact_mod_cast this

end BGHKLMM26.Hard
