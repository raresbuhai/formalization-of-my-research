module

public import BB20.Learning.Algorithm
public import Background.PolyTime.Rat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
import BB20.Machine.RunBounds
import BB20.Machine.Loop

/-!
# The running time of the structure-learning algorithms

With any threshold function computable in polynomial time, the algorithms of Theorems 6 and 11
run in time `O((|x| + 2)^c (n + 2)^{2^s})`.

The construction is in `BB20/Machine/`. The algorithms are run as one loop
(`BB20/Machine/Flat.lean`): `2n · n` phases, each a search through the `(n + 1)^k` words of `k`
digits `0, …, n` with `k = min(n, 2^s)` (`BB20/Machine/Search.lean`), whose rounds evaluate the
empirical proxy from the samples (`BB20/Machine/EffNu.lean`) in polynomial time
(`BB20/Machine/NuPolyTime.lean`, `BB20/Machine/StepPolyTime.lean`). The states stay polynomially
bounded (`BB20/Machine/RunBounds.lean`), and a loop of `a · b^k` rounds of polynomial time runs in
time `(a b^k + 1) · poly(|x|)` (`BB20.Machine.Loop.iterate_inTime`). Here `a = 2n²`, `b = n + 1`,
and `(n + 1)^k ≤ (n + 2)^{2^s}`.
-/

@[expose] public section

namespace BB20.Machine

open Turing.MultiTapeTM Run

/-- **The running time of the algorithm of Theorem 6.** -/
theorem alg6_runsInTime (thr : Input → Option ℚ)
    (hthr : ComputableInPolyTime thr encInput (encOption Encoding.encRat)) :
    ∃ c, RunsInTime encInput encOutput (alg6 thr) (learnTime c) := by
  have hinit := PT.init6_polytime hthr
  obtain ⟨c, hc⟩ := Loop.iterate_inTime (init6 thr) fstep finish (rounds6 thr)
    (fun x => capN x + 1) capK hinit PT.fstep_polytime PT.finish_polytime
    (PT.rounds6_polytime hthr) PT.base_polytime PT.capK_bin_polytime
    (fun x => 4 * (PT.encSt (init6 thr x)).length + 100 * ((encInput x).length + 1) ^ 4)
    (((PolyBounded.const 4).mul hinit.polyBounded_length).add
      ((PolyBounded.const 100).mul ((PolyBounded.self.add (.const 1)).pow 4)))
    (fun x => (abk_le x (rounds6_le thr x)).trans (Nat.le_add_left _ _))
    (fun x i _ => PT.length_iterate_le x _ _ false i)
  have hfun : (fun x => finish (fstep^[rounds6 thr x * (capN x + 1) ^ capK x] (init6 thr x))) =
      alg6 thr := funext (run6_eq thr)
  rw [hfun] at hc
  exact ⟨c + 2, 3 * c, hc.mono (fun x => time_le x (rounds6_le thr x) c)
    (fun x => time_le x (rounds6_le thr x) c)⟩

/-- **The running time of the algorithm of Theorem 11.** -/
theorem alg11_runsInTime (thr : Input → Option (ℚ × ℚ))
    (hthr : ComputableInPolyTime thr encInput
      (encOption (encPair Encoding.encRat Encoding.encRat))) :
    ∃ c, RunsInTime encInput encOutput (alg11 thr) (learnTime c) := by
  have hinit := PT.init11_polytime hthr
  obtain ⟨c, hc⟩ := Loop.iterate_inTime (init11 thr) fstep finish (rounds11 thr)
    (fun x => capN x + 1) capK hinit PT.fstep_polytime PT.finish_polytime
    (PT.rounds11_polytime hthr) PT.base_polytime PT.capK_bin_polytime
    (fun x => 4 * (PT.encSt (init11 thr x)).length + 100 * ((encInput x).length + 1) ^ 4)
    (((PolyBounded.const 4).mul hinit.polyBounded_length).add
      ((PolyBounded.const 100).mul ((PolyBounded.self.add (.const 1)).pow 4)))
    (fun x => (abk_le x (rounds11_le thr x)).trans (Nat.le_add_left _ _))
    (fun x i _ => PT.length_iterate_le x _ _ true i)
  have hfun : (fun x => finish (fstep^[rounds11 thr x * (capN x + 1) ^ capK x]
      (init11 thr x))) = alg11 thr := funext (run11_eq thr)
  rw [hfun] at hc
  exact ⟨c + 2, 3 * c, hc.mono (fun x => time_le x (rounds11_le thr x) c)
    (fun x => time_le x (rounds11_le thr x) c)⟩

end BB20.Machine
