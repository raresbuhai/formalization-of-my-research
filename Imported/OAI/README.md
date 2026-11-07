# Files from OpenAI's library

These files are copied from OpenAI's [`openai/math`](https://github.com/openai/math)
(Apache-2.0, see [LICENSE](LICENSE)), at commit `4eaee87548250b2682affda7d05d947c05554bae`. That
library is on Lean 4.34.1 and its own Mathlib, so it cannot be a dependency here.

They contain **Majority is Stablest**, `OAI.OptimalMaxCut.MISProof.majority_is_stablest`, for
balanced `[-1, 1]`-valued functions on the Boolean cube with small low-degree influences, together
with the real Walsh analysis it uses. The proof follows De, Mossel and Neeman
([Theory of Computing 12, 2016](https://theoryofcomputing.org/articles/v012a004/)): a Gaussian
Bellman function, its one-bit inequality, and tensorization over the cube, without the invariance
principle or Borell's theorem.

The paths, module names and namespaces are OpenAI's, except that `Walsh.lean` holds a section cut
out of a larger file. Each file starts with a comment giving its source and its changes. In short:

* `OAI/Computability/MaxCut/Walsh.lean`: the last section of `PCP/ContextLoad.lean` (real Walsh
  analysis); the rest of that file is about Turing machines and is not needed.
* `Estimates/Degree.lean`: without its section on the Goemans–Williamson ratio, which is unused.
* `Estimates/Density.lean`: two binders given their type, for our Mathlib's `ContinuousOn.comp`.
* `Estimates/Clip.lean`: only its first part, the namespace `OAI.OptimalMaxCut.MISProof`.
* `Gadgets/Polynomial.lean`, `Encoding/BitCube.lean`: unchanged.
* All files: module headers (`module`, `public import`, `@[expose] public section`) and imports of
  the needed parts of Mathlib instead of all of it.
