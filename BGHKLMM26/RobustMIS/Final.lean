module

public import BGHKLMM26.RobustMIS.Main
public import BGHKLMM26.RobustMIS.Sharp

/-!
# Robust Majority is Stablest

[BGHKLMM26, Theorem 7.1] with the error `C √η` (`BGHKLMM26.RobustMIS.robustMIS`): the transfer to
the cube (`robustMIS_of_sharp`, `Main.lean`) applied to the Gaussian lemma with the error `C √Δ`
(`gaussian_sharp`, `Sharp.lean`).
-/

public section

namespace BGHKLMM26.RobustMIS

/-- **Robust Majority is Stablest** [BGHKLMM26, Theorem 7.1]. -/
theorem robustMIS : BGHKLMM26.Hard.RobustMIS := robustMIS_of_sharp gaussian_sharp

end BGHKLMM26.RobustMIS
