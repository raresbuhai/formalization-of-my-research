# Formalized papers

Lean 4 formalizations of papers by [Rares-Darius Buhai](https://raresbuhai.com/), each with its main
results stated in `Challenge.lean` and proved in `Solution.lean`:

| Folder | Paper |
| --- | --- |
| [`BB20`](BB20) | Bresler, Buhai. *Learning restricted Boltzmann machines with sparse latent variables*. NeurIPS 2020. [arXiv:2006.04166](https://arxiv.org/abs/2006.04166) |
| [`BKS23`](BKS23) | Buhai, Kothari, Steurer. *Algorithms approaching the threshold for semi-random planted clique*. STOC 2023. [arXiv:2212.05619](https://arxiv.org/abs/2212.05619) |
| [`BS23`](BS23) | Buhai, Steurer. *Beyond parallel pancakes: quasi-polynomial time guarantees for non-spherical Gaussian mixtures*. COLT 2023. [arXiv:2112.05445](https://arxiv.org/abs/2112.05445) |
| [`BBKS24`](BBKS24) | Błasiok, Buhai, Kothari, Steurer. *Semirandom planted clique and the restricted isometry property*. FOCS 2024. [arXiv:2404.14159](https://arxiv.org/abs/2404.14159) |
| [`BHJK25`](BHJK25) | Buhai, Hsieh, Jain, Kothari. *The quasi-polynomial low-degree conjecture is false*. FOCS 2025. [arXiv:2505.17360](https://arxiv.org/abs/2505.17360) |
| [`BHSV25`](BHSV25) | Buhai, Hua, Steurer, Vári-Kakas. *Finding colorings in one-sided expanders*. [arXiv:2508.02825](https://arxiv.org/abs/2508.02825) |
| [`BCFGJPSSV26`](BCFGJPSSV26) | Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl. *A better-than-2 approximation for k-median*, Part I: *The power of general bids* and Part II: *Stable instances*. [arXiv:2610.18144](https://arxiv.org/abs/2610.18144), [arXiv:2610.17172](https://arxiv.org/abs/2610.17172) |
| [`BMW26`](BMW26) | Buhai, Mazzali, Wrzos-Kaminska. *Efficient recovery of latent coordinate structure from sparse observations of the hypercube*. [arXiv:2610.11741](https://arxiv.org/abs/2610.11741) |
| [`BGHKLMM26`](BGHKLMM26) | Buhai, Ghoshal, Huang, Kothari, Lee, Makarychev, Makarychev. *Optimal algorithms and hardness for Max-Cut in bounded degree graphs*. SODA 2027. [arXiv:2610.27216](https://arxiv.org/abs/2610.27216) |

A folder is named by the paper's citation key when the paper is added and keeps that name, even if
the paper later appears in a different year (`BGHKLMM26` appeared at SODA 2027).

All papers live in one Lake package and share one version of Mathlib. Algorithms and their running
times are formalized on top of
[complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of
the [CSLib](https://www.cslib.io/) community. It defines machine models and classes such as P, NP
and BPP, and its `polytime` tactic proves ordinary Lean functions polynomial-time on multi-tape
Turing machines. CSLib and Mathlib come with it, at the versions it pins.

## Layout

```
Background/                 shared material used by more than one paper
  SumOfSquares/             the sum-of-squares method (see its README.md)
Imported/                   libraries copied from elsewhere, adapted to our Lean and Mathlib
  TauCeti/                  from TauCeti: the Gaussian distribution function, Owen's T function,
                            Bernstein's inequality, and the Hermite basis of Gaussian L²
  OAI/                      from OpenAI's library: Majority is Stablest
  KMedian195/               from project-k-median: the 1.95 bound on a factor-revealing program
<Key>/
  Challenge.lean            the main results, stated without proof
  Model.lean                definitions the statements need (models, algorithms, encodings)
  Solution.lean             the same statements, proved
  comparator.json           which theorems lake comparator compares
  ...                       the development
```

Each paper is its own library: `lake build BKS23` builds one paper and what it imports, and
`lake build` builds everything. So are `Background` and each folder in `Imported/`. The imported
libraries keep the module names of their sources (`OAI.*`, not `Imported.OAI.*`), and each has a
README giving its source, licence and changes. Papers may import `Background` and the imported
libraries, but not each other.

Like Mathlib, files use Lean's module system: each starts with `module`, imports with
`public import`, and puts declarations in a `public section`.

## Checking a paper

To check what a paper proves, read its `Challenge.lean` and what that file imports (for `BKS23`,
`Model.lean`). Then run
`lake comparator` (see `lake help comparator`), which checks that `Solution.lean`
proves exactly those statements, is accepted by the kernel, and uses only the axioms listed in
`comparator.json`:

```sh
scripts/get-cache.sh  # download prebuilt Mathlib and complexitylib
lake comparator --inadvisably-no-sandbox --config BKS23/comparator.json
```

`--inadvisably-no-sandbox` skips the `bubblewrap` sandbox that `lake comparator` otherwise puts the
build in. The sandbox only exists on Linux and protects against malicious code in the project being
checked. CI runs the same command for every paper on each push.

## License

Apache-2.0, see [LICENSE](LICENSE). The files copied into `Imported/TauCeti` and `Imported/OAI`
are Apache-2.0 as well and keep their own `LICENSE` files and notices.

*Formalized by [Claude Code](https://claude.com/claude-code).*
