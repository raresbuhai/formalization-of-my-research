module

public import ABBKS26.Assembly.ExecRefineKernelsAuxSources
public import ABBKS26.Assembly.ExecRefineKernelsAuxFramePool
public import ABBKS26.Assembly.ExecRefineSourcesAuxVariance
public import ABBKS26.Assembly.ExecRefineBuilders

/-!
# Local data obligations for the executable refiner

The three source lemmas isolate construction of bounded rational local data. All source
certificates concern the same typed/list witness, cover arbitrary parent subsets, and pay
the whole level's storage. The proved compilers below supply metadata, Cartesian products,
threshold scanning, RB3 verification/merging, and the unconditional output caps.
The three source proofs now use the explicit bounded list builders and the synthesis
obligations in `ExecRefineBuilders`.

In particular a polynomial-time supplied P1 implementation does not, by itself, bound its
coefficient sizes by the fixed `need`. The first obligation permits constructing bounded
replacement certificates; it does not assert this false bound on unmodified P1 output.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth

open Common _root_.ABBKS26.Tree Sources
open Turing.MultiTapeTM ComputableInPolyTime

/-- Construct a rational eligible pool with bounded coefficients and a verified threshold
in the shared FAR case. No packing or choice of an empirical threshold is required here. -/
theorem exists_frobenius_source (F : FrameCode) (hF : FrameSpec F) :
    ∃ P : FrobSource, FrobCertificate P ∧ FrobGeometry F P := by
  obtain ⟨B, f, hf, hg⟩ := Synthesis.exists_frobenius_builder F hF
  exact ⟨Builders.frobSource B f, Synthesis.frobenius_representation B f hf, hg⟩

/-- A guarded centered moment/Z/net constructor returns the two unfiltered factors.
Its cap is on their product, and geometry refers to its new compatible Z witness. -/
theorem exists_spectral_source
    (F : FrameCode) (hF : FrameSpec F) (M : MomentCode) (hM : MomentSpec M)
    (N : NestedCode) (hN : NestedSpec N) (R : RoundCode) (hR : RoundSpecL R) :
    ∃ P : PairSource, PairCertificate .centered P ∧ PairCount .centered P ∧
      PairGeometry .centered F P := by
  obtain ⟨B, f, hf, hc, hg⟩ := Synthesis.exists_spectral_builder F hF M hM N hN R hR
  refine ⟨Builders.pairSource .centered B f, Synthesis.pair_representation _ B f hf,
    Synthesis.pair_product_bound _ B f ?_, hg⟩
  intro n d k ps x fuel h P
  simpa only [ite_true] using hc k ps x fuel h P

/-- The SUB constructor rounds and guards moments before its sparse high-degree call.
All mean statistics and all fixed threshold windows are returned as separate factors. -/
theorem exists_identical_source
    (F : FrameCode) (hF : FrameSpec F) (M : MomentCode) (hM : MomentSpec M)
    (N : NestedCode) (hN : NestedSpec N) (R : RoundCode) (hR : RoundSpecL R) :
    ∃ P : PairSource, PairCertificate .identical P ∧ PairCount .identical P ∧
      PairGeometry .identical F P := by
  obtain ⟨B, f, hf, hc, hg⟩ := Synthesis.exists_identical_builder F hF M hM N hN R hR
  refine ⟨Builders.pairSource .identical B f, Synthesis.pair_representation _ B f hf,
    Synthesis.pair_product_bound _ B f ?_, hg⟩
  intro n d k ps x fuel h P
  simpa only [reduceCtorEq, ite_false] using hc k ps x fuel h P

/-- The RB3 compiler is polynomial on all list inputs, without enumerating its binary cap. -/
theorem frob_source_polytime (P : FrobSource) (hP : FrobCertificate P) :
    ComputableInPolyTime ((frobKernel P).block .centered)
      (encPair encBlockArgs encUnary) (encList encEdge) := by
  have hd : ComputableInPolyTime (fun q : BlockArgs × ℕ ↦ q.1.1)
      (encPair encBlockArgs encUnary) encUnary := by fun_prop
  have hp : ComputableInPolyTime (fun q : BlockArgs × ℕ ↦ q.1.2.2.2.1)
      (encPair encBlockArgs encUnary) encPoints := by fun_prop
  have hh : ComputableInPolyTime (fun q : BlockArgs × ℕ ↦ q.1.2.2.2.2.1)
      (encPair encBlockArgs encUnary) encNat := by fun_prop
  have hn : ComputableInPolyTime (fun q : BlockArgs × ℕ ↦ q.1.2.2.2.2.2)
      (encPair encBlockArgs encUnary) encIndices := by fun_prop
  have hk : ComputableInPolyTime (fun q : BlockArgs × ℕ ↦ q.1.2.1)
      (encPair encBlockArgs encUnary) encNat := by fun_prop
  exact RB3.run_polytime hd
    (unary_to_binary.comp ((length_list _).comp hp)) hk (field_polytime 0)
    (field_polytime 3) hp
    (Thresholds.pool_polytime hd hh hp hn hP.polytime (field_polytime 6))

/-- Canonical agreement and edge envelopes survive threshold scanning and RB3 packing. -/
theorem frob_source_representation (P : FrobSource) (hP : FrobCertificate P) :
    KernelRepresentation .centered (frobKernel P) := by
  refine ⟨frob_source_polytime P hP, ?_, ?_, hP.storage⟩
  · intro x fuel hx _
    dsimp only
    intro h hh N
    let ps := Schedule.params .centered x.wmin x.k
    have ha := hP.agrees x.k ps (inputPoints x) fuel h N
    rw [args, points_input x hx] at ha
    change RB3.run _ _ _ _ _ _ _ = _
    rw [ha]
    have hfield (j : ℕ) : field ((dim x.points, x.k,
        (List.range x.k).map (fun i ↦ paramsList (ps i)), x.points, h, indexList N),
        fuel) j = (paramsList (ps h)).getD j 0 := by
      have hf := field_args x.k ps (inputPoints x) fuel h N (by omega) j
      rwa [args, points_input x hx] at hf
    rw [hfield 0, hfield 3, hfield 6]
    change RB3.run (dim x.points) x.points.length (ps h).w (ps h).verifyMass
      x.points x.k (Thresholds.poolL (dim x.points) x.points h (indexList N)
        ((P.pool x.k ps (inputPoints x) fuel h N).map
          (fun q ↦ (statisticList q.1, q.2))) (ps h).WF) = _
    rw [Thresholds.packed_pool_agrees (ps h)]
    have hd : (fun l ↦ vectorOf (dim x.points) (x.points.getD l.val [])) =
        inputPoints x := by
      funext l i
      simp [vectorOf, inputPoints, l.isLt]
    rw [hd]
    simp only [frobKernel, frobRaw, points_input x hx]
    rfl
  · intro x fuel hx hf
    dsimp only
    intro h hh N e he
    exact hP.edge_size x fuel hx hf h hh N e
      ((frobSplits_verified _ _ _ _ e he).1)

/-- Eligible variances and one FAR threshold suffice for the complete RB3 stage contract. -/
theorem frob_source_contract (F : FrameCode) (P : FrobSource)
    (hP : FrobGeometry F P) : CenteredStageContract F true (frobKernel P).run := by
  intro n d k ps x fuel h N
  refine ⟨frobSplits_bound _ _ _ _, ?_, ?_⟩
  · intro e he
    have hm := (frobSplits_verified _ _ _ _ e he).1
    obtain ⟨q, _, hq⟩ := (Thresholds.pool_mem _ _ _ _ _ e).mp hm
    have hp := Thresholds.raw_provenance _ _ _ _ _ e hq
    exact ⟨hp.1, hp.2.1⟩
  · intro M ε w η Δ D ω r I hx hp hf hh hI hl hN
    obtain ⟨hv, hc⟩ := hP k ps x fuel h N M ε w η Δ D ω r I hx hp hf hh hI hl hN
    have hready := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
    obtain ⟨hw, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := hready
    obtain ⟨hmass, _, hW, _⟩ := hm
    have hW0 : 0 ≤ (ps h).WF :=
      (show 0 ≤ 8 * (40 / (ps h).w) * sqrtUp (1 / (ps h).straddle) by
        unfold sqrtUp; positivity).trans hW
    have hmass' : ((ps h).windowMass : ℝ) ≤ 1 / 2 := by rw [hmass]; norm_num
    have hs := Thresholds.packed_pool_spec M I (ps h) (pointsOf x) h N
      (P.pool k ps x fuel h N) hW0 hmass' hv
    rw [points_decode] at hs
    refine ⟨fun e he ↦ (hs.2.1 e he).2.2.1, ?_⟩
    intro hcard hfar
    exact hs.2.2 (hc hcard hfar)

/-- Crossing the two factors preserves order, provenance, and the exact product count. -/
theorem pairs_agreement_count {n d : ℕ} (mode : Mode) (h : ℕ) (N : Finset (Fin n))
    (p : PairData d) :
    pairsL mode h (indexList N) (pairDataList p) = (pairs mode h N p).map edgeList ∧
      (pairs mode h N p).length = p.1.length * p.2.length ∧
      ∀ e ∈ pairs mode h N p, e.parent = N ∧ e.depth = h := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [pairsL, pairDataList, pairs, List.flatMap_map, List.map_flatMap,
      List.map_map]
    congr 1
    funext q
    congr 1
    funext t
    cases mode <;> rfl
  · simp [pairs, List.length_flatMap, List.map_const', List.sum_replicate, Nat.mul_comm]
  · intro e he
    obtain ⟨q, _, hm⟩ := List.mem_flatMap.mp he
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hm
    exact ⟨rfl, rfl⟩

/-- The unfiltered Cartesian compiler has an absolute polynomial degree on junk inputs. -/
theorem pair_source_representation (mode : Mode) (P : PairSource)
    (hP : PairCertificate mode P) : KernelRepresentation mode (pairKernel mode P) := by
  refine ⟨?_, ?_, hP.edge_size, hP.storage⟩
  · change ComputableInPolyTime (fun q ↦ pairsL mode _ _ (P.code q)) _ _
    unfold pairsL
    apply flatMapWithInput ((fst _ _).comp hP.polytime)
    apply mapWithInput (((snd _ _).comp hP.polytime).comp (fst _ _))
    unfold pairEdgeL
    cases mode <;> fun_prop
  · intro x fuel hx _
    dsimp only
    intro h _ N
    let ps := Schedule.params mode x.wmin x.k
    have ha := hP.agrees x.k ps (inputPoints x) fuel h N
    rw [args, points_input x hx] at ha
    change pairsL mode h (indexList N) _ = _
    rw [ha]
    exact (pairs_agreement_count mode h N _).1

/-- Spectral geometry and the reserved product cap give the complementary centered stage. -/
theorem spectral_source_contract (F : FrameCode) (P : PairSource)
    (hc : PairCount .centered P) (hg : PairGeometry .centered F P) :
    CenteredStageContract F false (pairKernel .centered P).run := by
  intro n d k ps x fuel h N
  have hp := pairs_agreement_count .centered h N (P.data k ps x fuel h N)
  refine ⟨hp.2.1.trans_le (hc k ps x fuel h N), hp.2.2, ?_⟩
  intro M ε w η Δ D ω r I hx hprep hf hh hI hl hN
  obtain ⟨hs, he⟩ := hg k ps x fuel h N M ε w η Δ D ω r I hx hprep hf hh hI hl hN
  constructor
  · intro e hem
    obtain ⟨q, hq, hm⟩ := List.mem_flatMap.mp hem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
    exact hs q hq t ht
  · intro hcard hfar
    obtain ⟨q, hq, t, ht, hv⟩ := he hcard (fun _ ↦ hfar)
    exact ⟨pairEdge .centered h N q t,
      List.mem_flatMap.mpr ⟨q, hq, List.mem_map.mpr ⟨t, ht, rfl⟩⟩, hv⟩

/-- The same unfiltered compiler gives the identical-covariance block contract. -/
theorem identical_source_contract (F : FrameCode) (P : PairSource)
    (hc : PairCount .identical P) (hg : PairGeometry .identical F P) :
    BlockContract .identical (pairKernel .identical P).run := by
  intro n d k ps x fuel h N
  have hp := pairs_agreement_count .identical h N (P.data k ps x fuel h N)
  refine ⟨hp.2.1.trans_le (hc k ps x fuel h N), hp.2.2, ?_⟩
  intro M ε w η Δ D ω r I hx hprep hf hh hI hl hN
  obtain ⟨hs, he⟩ := hg k ps x fuel h N M ε w η Δ D ω r I hx hprep hf hh hI hl hN
  constructor
  · intro e hem
    obtain ⟨q, hq, hm⟩ := List.mem_flatMap.mp hem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
    exact hs q hq t ht
  · intro hcard
    obtain ⟨q, hq, t, ht, hv⟩ := he hcard (by simp)
    exact ⟨pairEdge .identical h N q t,
      List.mem_flatMap.mpr ⟨q, hq, List.mem_map.mpr ⟨t, ht, rfl⟩⟩, hv⟩

end ABBKS26.Assembly.Exec.RefineSynth
