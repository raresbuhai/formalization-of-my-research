module

public import BHJK25.RS.Defs
public import BHJK25.RS.Planted.Bound
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Noisy planted tensors are accepted

[BHJK25, Lemma 2.11, planted case]: a planted tensor with noise `T_ε` is accepted with
probability at least `1 - exp(-n^(1 - 1/T))` for large `n`, when `ε T ≤ 1/5`. Acceptance and the
noise commute with relabelling, so the relabelling can be dropped; then the hidden layout is a
valid guess, and the true polynomial agrees with every column whose `2r` bits escaped the noise
(probability `(1 - ε/2)^{2r}` each, independently) and whose `α_v` is unique. Few columns have a
repeated `α_v`, since `q ≥ 16 n^{1 + 1/(2T)}`, and many escape the noise. The proof is in
`BHJK25/RS/Planted/`, assembled in `BHJK25.RS.PlantedAux.planted_bound_at`, with the shared facts
of `BHJK25/RS/Basic/` (parameter bounds, cells and the planted bits, relabelling).
-/

@[expose] public section

namespace BHJK25.RS

open MeasureTheory Filter

/-- **[BHJK25, Lemma 2.11, planted case]**: for `k ≥ 2`, `T ≥ 1` and `0 < ε` with `ε T ≤ 1/5`,
a planted tensor with noise `T_ε` is accepted with probability at least `1 - exp(-n^(1 - 1/T))`
for all large `n`. -/
theorem planted_bound {k T : ℕ} (hk : 2 ≤ k) (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε)
    (hεT : ε * T ≤ 1 / 5) :
    ∀ᶠ n : ℕ in atTop, 1 - Real.exp (-(n : ℝ) ^ (1 - 1 / (T : ℝ))) ≤
      noisyProb ε (planted k T n) (fun M ↦ Accept k T n M) := by
  filter_upwards [eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (3600 * (T : ℝ)),
    eventually_log_le one_pos (12 * ((k - 1 : ℕ) : ℝ)) (28 * ((k - 1 : ℕ) : ℝ)) one_pos]
    with n hn hlog hK
  rw [one_mul, Real.rpow_one] at hK
  exact PlantedAux.planted_bound_at hk hT hε hεT hn hlog (by linarith)

end BHJK25.RS
