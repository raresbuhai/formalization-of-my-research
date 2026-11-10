module

public import ABBKS26.Assembly.ExecRefineKernelsAuxFramePool

/-!
# Bounded list-source builders

The raw programs below return rational lists, without a typed implementation. Normalization
and decoding give agreement on every input. The Frobenius guard checks every scanned edge;
the pair guard checks the whole Cartesian product and empties both factors on failure.
Neither guard uses empirical verification. Budget limits may depend on unary fuel, but their
certified envelope and whole-level storage bound do not.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.Builders

open Common _root_.ABBKS26.Tree Sources
open Turing.MultiTapeTM ComputableInPolyTime

abbrev Args := BlockArgs × ℕ
abbrev encArgs := encPair encBlockArgs encUnary
abbrev PoolL := List (StatisticL × Bool)
abbrev encPool := encList (encPair encStatistic encBool)

/-- A binary local limit can be checked without writing that limit in unary. Its envelope
must pay for all parent subsets and the entire level, independently of global fuel. -/
structure Budget (mode : Mode) where
  limit : Args → ℕ
  bits : Input → ℕ
  polytime : ComputableInPolyTime limit encArgs encNat
  envelope : ∀ x fuel, Valid x → need mode x ≤ fuel →
    ∀ h, h < x.k - 1 → ∀ N,
      limit (args x.k (Schedule.params mode x.wmin x.k) (inputPoints x) h N, fuel) ≤
        bits x
  storage : ∀ x, Valid x → levelBits x.points.length x.k
    (branchCap mode x.k (Schedule.params mode x.wmin x.k)) (bits x) ≤ need mode x

/-- Size checks inspect binary encoding lengths, including metadata and thresholds. -/
def fits (b : ℕ) (es : List EdgeL) : Bool :=
  es.all fun e ↦ decide ((encEdge e).length ≤ b)

theorem fits_iff (b : ℕ) (es : List EdgeL) :
    fits b es = true ↔ ∀ e ∈ es, (encEdge e).length ≤ b := by
  simp [fits, List.all_eq_true]

@[fun_prop] theorem fits_polytime {α : Type} {input : α ↪ List Bool}
    {b : α → ℕ} {es : α → List EdgeL}
    (hb : ComputableInPolyTime b input encNat)
    (he : ComputableInPolyTime es input (encList encEdge)) :
    ComputableInPolyTime (fun a ↦ fits (b a) (es a)) input encBool := by
  unfold fits
  apply allWithInput he
  apply binary_le' _ (hb.comp (fst _ _))
  exact unary_to_binary.comp (.of_tidy
    ((ComputableTidilyInPolyTime.encoding_length encEdge).comp (snd _ _).tidy))

/-- Normalize shapes before checking the scanned thresholds of each paired certificate. -/
def frobCode (B : Budget .centered) (f : Args → PoolL) (a : Args) : PoolL :=
  ((f a).map fun q ↦ (FramePool.canonical a.1.1 q.1, q.2)).filter fun q ↦
    fits (B.limit a) (Thresholds.rawL a.1.1 a.1.2.2.2.1 a.1.2.2.2.2.1
      a.1.2.2.2.2.2 q.1 (field a 6))

/-- Typed statistics are decoded from the guarded list, so all guarantees use one witness. -/
def frobSource (B : Budget .centered) (f : Args → PoolL) : FrobSource where
  code := frobCode B f
  pool k ps x fuel h N :=
    (frobCode B f (args k ps x h N, fuel)).map fun q ↦ (statisticOf _ q.1, q.2)
  bits := B.bits

private theorem frob_normal (B : Budget .centered) (f : Args → PoolL) (a : Args)
    (q : StatisticL × Bool) (hq : q ∈ frobCode B f a) :
    statisticList (statisticOf a.1.1 q.1) = q.1 := by
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hq).1
  rw [FramePool.canonical_agrees, statistic_roundtrip]

theorem frob_agrees (B : Budget .centered) (f : Args → PoolL)
    {n d : ℕ} (k : ℕ) (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (N : Finset (Fin n)) :
    (frobSource B f).code (args k ps x h N, fuel) =
      ((frobSource B f).pool k ps x fuel h N).map
        (fun q ↦ (statisticList q.1, q.2)) := by
  simp only [frobSource, List.map_map]
  symm
  calc
    _ = (frobCode B f (args k ps x h N, fuel)).map id := by
      apply List.map_congr_left
      intro q hq
      exact Prod.ext (frob_normal B f _ q hq) rfl
    _ = _ := List.map_id _

theorem frob_polytime (B : Budget .centered) (f : Args → PoolL)
    (hf : ComputableInPolyTime f encArgs encPool) :
    ComputableInPolyTime (frobCode B f) encArgs encPool := by
  unfold frobCode
  apply filterWithInput
  · apply mapWithInput hf
    exact (FramePool.canonical_polytime (by fun_prop) (by fun_prop)).prod (by fun_prop)
  · apply fits_polytime (B.polytime.comp (fst _ _))
    exact Thresholds.raw_polytime (by fun_prop) (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop) ((field_polytime 6).comp (fst _ _))

/-- The guard bounds raw scanned records, before RB3 has removed any of them. -/
theorem frob_certificate (B : Budget .centered) (f : Args → PoolL)
    (hf : ComputableInPolyTime f encArgs encPool) : FrobCertificate (frobSource B f) := by
  refine ⟨frob_polytime B f hf, frob_agrees B f, ?_, B.storage⟩
  intro x fuel hx hfu h hh N e he
  obtain ⟨q, hq, he⟩ := (Thresholds.pool_mem _ _ _ _ _ e).mp he
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hq
  have hstat : statisticOf (dim x.points) p.1 = q := congrArg Prod.fst heq
  have hnormal := frob_normal B f _ p hp
  change statisticList (statisticOf (dim x.points) p.1) = p.1 at hnormal
  have hfit := (fits_iff _ _).mp (List.mem_filter.mp hp).2
  have he' : edgeList e ∈ Thresholds.rawL (dim x.points) (pointsOf (inputPoints x))
      h (indexList N) p.1 (Schedule.params .centered x.wmin x.k h).WF := by
    rw [← hnormal, Thresholds.raw_agrees, hstat]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have hf6 : field (args x.k (Schedule.params .centered x.wmin x.k)
      (inputPoints x) h N, fuel) 6 = (Schedule.params .centered x.wmin x.k h).WF := by
    rw [field_args _ _ _ _ _ _ (by omega)]
    rfl
  change ∀ e ∈ Thresholds.rawL (dim x.points) (pointsOf (inputPoints x)) h
    (indexList N) p.1 (field (args x.k (Schedule.params .centered x.wmin x.k)
      (inputPoints x) h N, fuel) 6), _ at hfit
  rw [hf6] at hfit
  exact (hfit _ he').trans (B.envelope x fuel hx hfu h hh N)

/-- Canonical shapes are fixed before the Cartesian bit check. -/
def pairNormal (d : ℕ) (p : PairDataL) : PairDataL :=
  (p.1.map (FramePool.canonical d), p.2)

/-- A failed bit check discards just this block's two factors. -/
def pairCode (mode : Mode) (B : Budget mode) (f : Args → PairDataL)
    (a : Args) : PairDataL :=
  let p := pairNormal a.1.1 (f a)
  if fits (B.limit a) (pairsL mode a.1.2.2.2.2.1 a.1.2.2.2.2.2 p) then p else ([], [])

def pairSource (mode : Mode) (B : Budget mode) (f : Args → PairDataL) : PairSource where
  code := pairCode mode B f
  data k ps x fuel h N :=
    let p := pairCode mode B f (args k ps x h N, fuel)
    (p.1.map (statisticOf _), p.2)
  bits := B.bits

private theorem pair_normal (mode : Mode) (B : Budget mode) (f : Args → PairDataL)
    (a : Args) (q : StatisticL) (hq : q ∈ (pairCode mode B f a).1) :
    statisticList (statisticOf a.1.1 q) = q := by
  dsimp only [pairCode] at hq
  split_ifs at hq
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hq
    rw [FramePool.canonical_agrees, statistic_roundtrip]
  · simp at hq

theorem pair_agrees (mode : Mode) (B : Budget mode) (f : Args → PairDataL)
    {n d : ℕ} (k : ℕ) (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (N : Finset (Fin n)) :
    (pairSource mode B f).code (args k ps x h N, fuel) =
      pairDataList ((pairSource mode B f).data k ps x fuel h N) := by
  apply Prod.ext
  · simp only [pairSource, pairDataList, List.map_map]
    symm
    calc
      _ = ((pairCode mode B f (args k ps x h N, fuel)).1).map id := by
        apply List.map_congr_left
        intro q hq
        exact pair_normal mode B f _ q hq
      _ = _ := List.map_id _
  · rfl

private theorem pairs_polytime (mode : Mode) {α : Type} {input : α ↪ List Bool}
    {h : α → ℕ} {N : α → List ℕ} {p : α → PairDataL}
    (hh : ComputableInPolyTime h input encNat)
    (hN : ComputableInPolyTime N input encIndices)
    (hp : ComputableInPolyTime p input encPairData) :
    ComputableInPolyTime (fun a ↦ pairsL mode (h a) (N a) (p a))
      input (encList encEdge) := by
  unfold pairsL
  apply flatMapWithInput ((fst _ _).comp hp)
  apply mapWithInput (((snd _ _).comp hp).comp (fst _ _))
  unfold pairEdgeL
  cases mode <;> fun_prop

theorem pair_polytime (mode : Mode) (B : Budget mode) (f : Args → PairDataL)
    (hf : ComputableInPolyTime f encArgs encPairData) :
    ComputableInPolyTime (pairCode mode B f) encArgs encPairData := by
  have hp : ComputableInPolyTime (fun a : Args ↦ pairNormal a.1.1 (f a))
      encArgs encPairData := by
    apply ComputableInPolyTime.prod
    · apply mapWithInput ((fst _ _).comp hf)
      exact FramePool.canonical_polytime (by fun_prop) (by fun_prop)
    · exact (snd _ _).comp hf
  unfold pairCode
  exact ite_decide (fits_polytime B.polytime
    (pairs_polytime mode (by fun_prop) (by fun_prop) hp)) hp (const ([], []))

/-- The guard is independent of Verify and checks every retained statistic/window pair. -/
theorem pair_certificate (mode : Mode) (B : Budget mode) (f : Args → PairDataL)
    (hf : ComputableInPolyTime f encArgs encPairData) :
    PairCertificate mode (pairSource mode B f) := by
  refine ⟨pair_polytime mode B f hf, pair_agrees mode B f, ?_, B.storage⟩
  intro x fuel hx hfu h hh N e he
  let a := (args x.k (Schedule.params mode x.wmin x.k) (inputPoints x) h N, fuel)
  have ha := pair_agrees mode B f x.k (Schedule.params mode x.wmin x.k)
    (inputPoints x) fuel h N
  change pairCode mode B f a = _ at ha
  have he' : edgeList e ∈ pairsL mode h (indexList N) (pairCode mode B f a) := by
    rw [ha]
    obtain ⟨q, hq, hmap⟩ := List.mem_flatMap.mp he
    obtain ⟨t, htm, rfl⟩ := List.mem_map.mp hmap
    apply List.mem_flatMap.mpr
    refine ⟨statisticList q, List.mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
    exact List.mem_map.mpr ⟨t, htm, by cases mode <;> rfl⟩
  have hfit : fits (B.limit a) (pairsL mode h (indexList N) (pairCode mode B f a)) =
      true := by
    change fits (B.limit a)
      (pairsL mode a.1.2.2.2.2.1 a.1.2.2.2.2.2 (pairCode mode B f a)) = true
    dsimp only [pairCode]
    split_ifs with hg
    · exact hg
    · simp [pairsL, fits]
  exact ((fits_iff _ _).mp hfit _ he').trans (B.envelope x fuel hx hfu h hh N)

/-- Shape normalization preserves factor lengths; a failed bit guard only decreases them. -/
theorem pair_count (mode : Mode) (B : Budget mode) (f : Args → PairDataL)
    (hc : ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h N,
      let p := f (args k ps x h N, fuel)
      p.1.length * p.2.length ≤
        if mode = .centered then centeredStageCap false k (ps h)
        else stepBranchCap .identical k (ps h)) :
    PairCount mode (pairSource mode B f) := by
  intro n d k ps x fuel h N
  have hcount := hc k ps x fuel h N
  dsimp only [pairSource, pairCode]
  split
  · simpa only [pairNormal, List.length_map] using hcount
  · simp

end ABBKS26.Assembly.Exec.RefineSynth.Builders
