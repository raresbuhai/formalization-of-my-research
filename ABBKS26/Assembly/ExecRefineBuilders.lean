module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobStable
public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecComplete
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdEnvelope
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdAllowanceBound

/-!
# List-program synthesis obligations for bounded refinement sources

The builders discharge shape normalization, typed/list agreement, polynomial-time output
checks, and bounds for every returned edge on arbitrary parent subsets. Synthesis below
must still supply a binary budget evaluator with a fuel-independent, whole-level envelope.
Geometry is deliberately about the guarded source: neither polynomial time nor an output
check proves that a separator survives that check.

The two remaining synthesis obligations concern rational list programs, not a choice of a
classical subspace witness. The Frobenius constructor below also discharges its bit budget.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.Synthesis

open Common _root_.ABBKS26.Tree Sources Builders
open Turing.MultiTapeTM ComputableInPolyTime

/-- Normalization, decoding and the scanned-edge guard give a full Frobenius certificate
from just the raw program's machine certificate and its local budget. -/
theorem frobenius_representation (B : Budget .centered) (f : Args → PoolL)
    (hf : ComputableInPolyTime f encArgs encPool) : FrobCertificate (frobSource B f) := by
  exact frob_certificate B f hf

/-- The pair builder supplies both agreement and a uniform bit envelope for every pair;
all its list operations have a polynomial-time certificate on junk inputs too. -/
theorem pair_representation (mode : Mode) (B : Budget mode) (f : Args → PairDataL)
    (hf : ComputableInPolyTime f encArgs encPairData) :
    PairCertificate mode (pairSource mode B f) := by
  exact pair_certificate mode B f hf

/-- No Cartesian expansion or hard-cap enumeration is needed to preserve the raw product
allowance. Normalization preserves lengths and the bit guard can only empty the factors. -/
theorem pair_product_bound (mode : Mode) (B : Budget mode) (f : Args → PairDataL)
    (hc : ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h P,
      let p := f (args k ps x h P, fuel)
      p.1.length * p.2.length ≤
        if mode = .centered then centeredStageCap false k (ps h)
        else stepBranchCap .identical k (ps h)) :
    PairCount mode (pairSource mode B f) := by
  exact pair_count mode B f hc


/-- Every raw certificate whose scanned edges fit the local limit survives with its original
flag and decoded quadratic. This is the good-path condition needed by the FAR proof. -/
theorem frobenius_retains (B : Budget .centered) (f : Args → PoolL)
    {n d : ℕ} (k : ℕ) (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) (q : StatisticL × Bool)
    (hq : q ∈ f (args k ps x h P, fuel))
    (hsize : ∀ e ∈ Thresholds.rawL d (pointsOf x) h (indexList P)
      (FramePool.canonical d q.1) (ps h).WF,
      (encEdge e).length ≤ B.limit (args k ps x h P, fuel)) :
    (statisticOf d q.1, q.2) ∈ (frobSource B f).pool k ps x fuel h P := by
  apply List.mem_map.mpr
  refine ⟨(FramePool.canonical d q.1, q.2), ?_, ?_⟩
  · apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
    apply (fits_iff _ _).mpr
    have hw : field (args k ps x h P, fuel) 6 = (ps h).WF := by
      rw [field_args _ _ _ _ _ _ hh]
      rfl
    change ∀ e ∈ Thresholds.rawL d (pointsOf x) h (indexList P)
      (FramePool.canonical d q.1) (field (args k ps x h P, fuel) 6), _
    rwa [hw]
  · exact Prod.ext (by rw [FramePool.canonical_agrees, statistic_roundtrip]) rfl


private def frobPrecision (a : Args) : ℕ :=
  FrobPrecision.precision (FrobBounds.exponent a)

private def frobContraction (a : Args) : ℚ :=
  FrobPrecision.contraction (FrobBounds.exponent a)

private theorem prepared_rounding_bounds {n k d : ℕ} (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (N : Finset (Fin n))
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps) (hh : h < k - 1)
    (hl : leakage ω N I ≤ leakageBudget ps η h) (hN : w * n / 4 ≤ N.card) :
    let a := (args k ps x h N, fuel)
    let c := (FrobBounds.covBound a : ℝ)
    0 ≤ c ∧ (∀ j ∈ I, ∀ v, qform (M.S j) v ≤ c * sqnorm v) ∧
      2 * c ^ 2 * ((d : ℝ) * (1 / (2 : ℝ) ^ frobPrecision a)) ^ 2 ≤
        (1 - (frobContraction a : ℝ)) ^ 2 * (40 / ((ps h).w : ℝ)) ^ 2 ∧
      (1 - (frobContraction a : ℝ)) * ((ps h).R : ℝ) +
        2 * (d : ℝ) ^ 2 * (1 / (2 : ℝ) ^ frobPrecision a) * c ≤ 1 / 2 := by
  let a : Args := (args k ps x h N, fuel)
  let z := FrobBounds.exponent a
  let c := (FrobBounds.covBound a : ℝ)
  have hr := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  have hw : (0 : ℝ) < (ps h).w := by exact_mod_cast hr.1
  have hw2 : ((ps h).w : ℝ) ≤ 1 / 2 := by
    have hb := Rat.cast_le (K := ℝ) |>.mpr hr.2.1
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hb
    exact hb
  have he := FrobBounds.covBound_agrees k ps x fuel h N (by omega)
  have hc : 0 ≤ c := by
    dsimp only [c, a]
    rw [he]
    positivity
  have hupper := FrobBounds.prepared_cov_upper ps x h N M ε w η Δ D ω r I hI
    hx hp hh hl hN
  rw [← he] at hupper
  have hd : (d : ℝ) ≤ (2 : ℝ) ^ z := FrobBounds.exponent_dim a
  have hB : (1 : ℝ) ≤ 40 / ((ps h).w : ℝ) := by
    apply (le_div_iff₀ hw).mpr
    linarith only [hw2]
  have hR : ((ps h).R : ℝ) ≤ (2 : ℝ) ^ z := by
    have hb := FrobBounds.exponent_radius a
    have hfield : field a 8 = (ps h).R := by
      rw [field_args _ _ _ _ _ _ (by omega)]
      rfl
    rwa [hfield] at hb
  exact ⟨hc, hupper, FrobPrecision.variance_precision z d c _ hc
    (FrobBounds.exponent_cov a) hd hB,
    FrobPrecision.center_loss z d c _ hc (FrobBounds.exponent_cov a) hd hR⟩

private theorem rounded_complete_of_bounds {n k d : ℕ}
    (B : Budget .centered) (F : FrameCode) (hF : FrameSpec F) (b : Args → ℕ)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (N : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω N I ≤ leakageBudget ps η h) (hN : w * n / 4 ≤ N.card)
    (hcard : 2 ≤ I.card) (hfar : centeredFar F M ω r (ps h) fuel N I hI)
    (hmag : ∀ q, (q, true) ∈ FrobPure.pool F (ps h) x fuel N → ∀ i j,
      |frobContraction (args k ps x h N, fuel) * q.A i j| ≤
        2 ^ b (args k ps x h N, fuel))
    (hsize : ∀ q, (q, true) ∈ FrobPure.pool F (ps h) x fuel N →
      ∀ e ∈ Thresholds.rawL d (pointsOf x) h (indexList N)
        (FrobRound.roundedL d (frobPrecision (args k ps x h N, fuel))
          (b (args k ps x h N, fuel)) (frobContraction (args k ps x h N, fuel))
            (statisticList q)) (ps h).WF,
        (encEdge e).length ≤ B.limit (args k ps x h N, fuel)) :
    ∃ q, (q, true) ∈ (frobSource B
      (FrobRound.run F frobPrecision b frobContraction)).pool k ps x fuel h N ∧
        ∃ t, Verify (ps h) x (Thresholds.typedEdge h N q (ps h).WF t) := by
  let a : Args := (args k ps x h N, fuel)
  obtain ⟨q, hq, hgap⟩ := FrobStable.far_trace_witness F hF ps x fuel h N M ε w η Δ D
    ω r I hI hx hp hfar
  have hsym := FrobRound.pool_symmetric F hF (ps h) x fuel N q hq
  obtain ⟨hc, hupper, hprec, hloss⟩ := prepared_rounding_bounds ps x fuel h N
    M ε w η Δ D ω r I hI hx hp hh hl hN
  have hv := FrobPure.prepared_variance F hF ps x fuel h N M ε w η Δ D ω r I hI
    hx hp hf hh hl hN q hq
  have hv' (j : Fin k) (hj : j ∈ I) : ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ (FrobPure.pure q).eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 (M.S j)) ≤
        (40 / ((ps h).w : ℝ)) ^ 2 := by
    have hvj := hv j hj
    rw [hp.2.1 j, WithLp.toLp_zero] at hvj
    exact (FrobPure.variance_le q hsym (M.S j) (hp.1.posDef j).posSemidef).trans hvj
  have hs := FrobPrecision.contraction_nonneg (FrobBounds.exponent a)
  have hs1 := FrobPrecision.contraction_lt_one (FrobBounds.exponent a)
  obtain ⟨t, ht⟩ := FrobStable.rounded_recorded M ε w η Δ D ω r ps hp h hh N I hcard
    hl hN q hsym (frobPrecision a) (b a) (frobContraction a) (FrobBounds.covBound a)
    hs hs1 hc hupper hv' (hmag q hq) hprec hgap hloss
  let q' := FrobRound.rounded (frobPrecision a) (b a) (frobContraction a) q
  let qL := FrobRound.roundedL d (frobPrecision a) (b a) (frobContraction a)
    (statisticList q)
  have hraw : (qL, true) ∈ FrobRound.run F frobPrecision b frobContraction a := by
    apply List.mem_map.mpr
    refine ⟨(statisticList q, true), List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · rw [FrobPure.run_agrees F k ps x fuel h N (by omega)]
      exact List.mem_map.mpr ⟨(q, true), hq, rfl⟩
    · apply (FrobRound.magFits_iff d (b a) (frobContraction a) (statisticList q)).mpr
      simpa only [statistic_roundtrip] using hmag q hq
  have hcanon : FramePool.canonical d qL = qL := by
    simp only [qL, FramePool.canonical_agrees, FrobRound.roundedL_agrees,
      statistic_roundtrip]
  have hretain := frobenius_retains B (FrobRound.run F frobPrecision b frobContraction)
    k ps x fuel h N (by omega) (qL, true) hraw (by
      rw [hcanon]
      exact hsize q hq)
  have hdecode : statisticOf d qL = q' := by
    simp only [qL, FrobRound.roundedL_agrees, statistic_roundtrip, q']
  rw [hdecode] at hretain
  exact ⟨q', hretain, t, hx ▸ ht⟩

private def FrobGridFits (F : FrameCode) (B : Budget .centered) (b : Args → ℕ) : Prop :=
  ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h N,
    ∀ (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d) r (I : Finset (Fin k)),
      x = (fun l i ↦ r ((ω l).1, (ω l).2.2) i) →
      Prepared .centered M ε w η Δ D ω r ps →
      localBudget .centered k n d ps ≤ fuel → h < k - 1 →
      I.Nonempty → leakage ω N I ≤ leakageBudget ps η h → w * n / 4 ≤ N.card →
      ∀ q, (q, true) ∈ FrobPure.pool F (ps h) x fuel N →
        (∀ i j, |frobContraction (args k ps x h N, fuel) * q.A i j| ≤
          2 ^ b (args k ps x h N, fuel)) ∧
        ∀ e ∈ Thresholds.rawL d (pointsOf x) h (indexList N)
          (FrobRound.roundedL d (frobPrecision (args k ps x h N, fuel))
            (b (args k ps x h N, fuel)) (frobContraction (args k ps x h N, fuel))
              (statisticList q)) (ps h).WF,
          (encEdge e).length ≤ B.limit (args k ps x h N, fuel)

private theorem geometry_of_grid (F : FrameCode) (hF : FrameSpec F)
    (B : Budget .centered) (b : Args → ℕ) (hgrid : FrobGridFits F B b) :
    FrobGeometry F (frobSource B (FrobRound.run F frobPrecision b frobContraction)) := by
  intro n d k ps x fuel h N M ε w η Δ D ω r I hx hp hf hh hI hl hN
  let a : Args := (args k ps x h N, fuel)
  obtain ⟨hc, hupper, hprec, _⟩ := prepared_rounding_bounds ps x fuel h N
    M ε w η Δ D ω r I hI hx hp hh hl hN
  have hs := FrobPrecision.contraction_nonneg (FrobBounds.exponent a)
  have hs1 := FrobPrecision.contraction_lt_one (FrobBounds.exponent a)
  refine ⟨?_, ?_⟩
  · intro q hq
    exact FrobRound.validity B F hF frobPrecision b frobContraction ps x fuel h N
      M ε w η Δ D ω r I hI hx hp hf hh hl hN (FrobBounds.covBound a) hc hs hs1
        hupper hprec q hq
  · intro hcard hfar
    have hg := hgrid k ps x fuel h N M ε w η Δ D ω r I hx hp hf hh hI hl hN
    exact rounded_complete_of_bounds B F hF b ps x fuel h N M ε w η Δ D ω r I hI
      hx hp hf hh hl hN hcard hfar (fun q hq ↦ (hg q hq).1) (fun q hq ↦ (hg q hq).2)

private theorem grid_of_floor (F : FrameCode) (hF : FrameSpec F)
    (hfloor : FrobCap.PreparedFloor FrobScan.coefficientExponent)
    (hencoding : FrobStorage.CanonicalEnvelope FrobScan.limit) :
    FrobGridFits F (FrobStorage.budget FrobScan.limit FrobScan.limit_polytime hencoding)
      FrobScan.coefficientExponent := by
  intro n d k ps x fuel h N M ε w η Δ D ω r I hx hp hf hh hI hl hN q hq
  let a : Args := (args k ps x h N, fuel)
  have hs : 0 ≤ frobContraction a := by
    exact_mod_cast FrobPrecision.contraction_nonneg (FrobBounds.exponent a)
  have hs1 : frobContraction a ≤ 1 := by
    exact_mod_cast (FrobPrecision.contraction_lt_one (FrobBounds.exponent a)).le
  refine ⟨FrobCap.prepared_entries F hF FrobScan.coefficientExponent hfloor ps x
    fuel h N M ε w η Δ D ω r I hI hx hp hf hh hl hN (frobContraction a) hs hs1 q hq, ?_⟩
  have hscan := FrobScan.rounded_scan a (frobPrecision a)
    (FrobScan.coefficientExponent a) (frobContraction a) (statisticList q)
      (FrobScan.precision_bound a)
  have hw : field a 6 = (ps h).WF := by
    rw [field_args _ _ _ _ _ _ (by omega)]
    rfl
  rw [hw] at hscan
  exact hscan

/-- Synthesize bounded eligible quadratic lists whose guarded pool is valid and FAR-complete.
The constructor need not provide a separate typed implementation or prove scan bit bounds. -/
theorem exists_frobenius_builder (F : FrameCode) (hF : FrameSpec F) :
    ∃ (B : Budget .centered) (f : Args → PoolL),
      ComputableInPolyTime f encArgs encPool ∧ FrobGeometry F (frobSource B f) := by
  suffices hg : ∃ (B : Budget .centered) (b : Args → ℕ),
      ComputableInPolyTime b encArgs encUnary ∧ FrobGridFits F B b by
    obtain ⟨B, b, hb, hgrid⟩ := hg
    refine ⟨B, FrobRound.run F frobPrecision b frobContraction, ?_,
      geometry_of_grid F hF B b hgrid⟩
    exact FrobRound.run_polytime F hF frobPrecision b frobContraction
      (FrobPrecision.precision_polytime FrobBounds.exponent_polytime) hb
      (FrobPrecision.contraction_polytime FrobBounds.exponent_polytime)
  suffices hs : FrobCap.PreparedFloor FrobScan.coefficientExponent ∧
      FrobStorage.CanonicalEnvelope FrobScan.limit by
    exact ⟨FrobStorage.budget FrobScan.limit FrobScan.limit_polytime hs.2,
      FrobScan.coefficientExponent, FrobScan.coefficientExponent_polytime,
      grid_of_floor F hF hs.1 hs.2⟩
  exact ⟨FrobFloor.prepared_floor, FrobEncoding.canonical_envelope⟩

/-- Synthesize the unfiltered centered statistic/window factors with the reserved product
cap. The compatible Z witness and its net must remain complete after the bit check. -/
theorem exists_spectral_builder
    (F : FrameCode) (hF : FrameSpec F) (M : MomentCode) (hM : MomentSpec M)
    (N : NestedCode) (hN : NestedSpec N) (R : RoundCode) (hR : RoundSpecL R) :
    ∃ (B : Budget .centered) (f : Args → PairDataL),
      ComputableInPolyTime f encArgs encPairData ∧
      (∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h P,
        let p := f (args k ps x h P, fuel)
        p.1.length * p.2.length ≤ centeredStageCap false k (ps h)) ∧
      PairGeometry .centered F (pairSource .centered B f) := by
  suffices hs : ∃ g : Args → Points,
      ComputableInPolyTime g encArgs encPoints ∧
      (∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h P,
        let p := SpecGuard.run g (args k ps x h P, fuel)
        p.1.length * p.2.length ≤ centeredStageCap false k (ps h)) ∧
      SpecGuard.Complete F g by
    obtain ⟨g, hg, hcount, hcomplete⟩ := hs
    exact ⟨SpecSquare.budget, SpecGuard.run g, SpecGuard.run_polytime g hg,
      hcount, SpecGuard.geometry_of_complete F g hcomplete⟩
  refine ⟨SpecProgram.directions F M N R,
    SpecProgram.directions_polytime F hF M hM N hN R hR, ?_, ?_⟩
  · intro n d k ps x fuel h P
    exact SpecProgram.count F M N R k ps x fuel h P
  · exact SpecComplete.complete F hF M hM N hN R hR

/-- Synthesize guarded SUB/net factors and fixed mean windows with their product cap.
Global sample fuel must not occur in the sparse high-degree problem payload. -/
theorem exists_identical_builder
    (F : FrameCode) (_hF : FrameSpec F) (M : MomentCode) (hM : MomentSpec M)
    (N : NestedCode) (hN : NestedSpec N) (R : RoundCode) (hR : RoundSpecL R) :
    ∃ (B : Budget .identical) (f : Args → PairDataL),
      ComputableInPolyTime f encArgs encPairData ∧
      (∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h P,
        let p := f (args k ps x h P, fuel)
        p.1.length * p.2.length ≤ stepBranchCap .identical k (ps h)) ∧
      PairGeometry .identical F (pairSource .identical B f) := by
  suffices hs : ∃ g : Args → IdGuard.Statistics,
      ComputableInPolyTime g encArgs IdGuard.encStatistics ∧
      (∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h P, h < k →
        (g (args k ps x h P, fuel)).length ≤
          netBound (IdCov.N_pack (ps h).subspaceAccuracy k) (ps h).subspaceAccuracy) ∧
      IdGuard.Valid g ∧ IdGuard.Complete g by
    obtain ⟨g, hg, hcount, hvalid, hcomplete⟩ := hs
    refine ⟨IdGuard.budget, IdGuard.run g, IdGuard.run_polytime g hg, ?_,
      IdGuard.geometry F g hvalid hcomplete⟩
    intro n d k ps x fuel h P
    exact IdGuard.count g k ps x fuel h P (hcount k ps x fuel h P)
  suffices hs : IdGuard.Valid (IdProgram.statistics M N R) ∧
      IdGuard.Complete (IdProgram.statistics M N R) by
    refine ⟨IdProgram.statistics M N R,
      IdProgram.statistics_polytime M hM N hN R hR, ?_, hs.1, hs.2⟩
    intro n d k ps x fuel h P hh
    exact IdProgram.count M N R k ps x fuel h P hh
  suffices hb : IdAllowance.Prepared M N by
    exact IdFinish.certificate M hM N hN R hR hb (IdEnvelope.prepared M hM N R)
  exact IdAllowanceBound.prepared M hM N hN


end ABBKS26.Assembly.Exec.RefineSynth.Synthesis
