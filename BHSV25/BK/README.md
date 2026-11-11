# Bansal–Khot from the Unique Games Conjecture

`BHSV25.bansalKhot : UniqueGames.KhotUGC → BHSV25.BansalKhot`
([../BansalKhot.lean](../BansalKhot.lean)) is `BHSV25.BK.bansalKhot_of` applied to the hardness of
left-regular instances, `BHSV25.BK.LRHard`, which `../UG/` derives from the conjecture
(`BHSV25.UG.lrHard_of_khotUGC`, see below), and to the analytic theorem `BHSV25.BK.itAintOver`,
"It Ain't Over Till It's Over" [MOO10, Theorem 4.9]. Everything uses only `propext`, `Classical.choice` and
`Quot.sound`.

| File | Content |
| --- | --- |
| `Basic.lean` | Copied from BGHKLMM26: tables, influences, KKMO decoding (`few_bad`). |
| `AintOver.lean` | The analytic theorem: statements, moment form from probability form. |
| `Invariance*.lean` | Copied from BGHKLMM26/RobustMIS: Bonami, Lindeberg, mollification, invariance. |
| `Ensemble.lean` | The three-valued ensemble of a random subcube (`law3`, `subcube_eq`). |
| `HyperReverse.lean` | Reverse hypercontractivity on the cube (`rev_hc`, `few_high`). |
| `AintProof.lean` | Proof of the analytic theorem (`Aint.itAintOverProb_main`). |
| `Graph.lean` | The reduction (`Prm.reduce`), copies, cliques, restated `bkGap'`. |
| `Vertices.lean` | Vertex numbering (`Prm.vEquiv`, `Prm.rv_eq`), demands as subcubes. |
| `Copies.lean` | Degrees and independent sets of disjoint copies. |
| `Complete.lean` | Completeness (`Prm.complete`). |
| `Sound.lean` | Soundness (`Prm.sound`), folded long codes. |
| `Machine.lean` | Polynomial time (`Prm.reduce_polytime`). |
| `Main.lean` | Parameters and assembly (`bansalKhot_of`). |
| `../UG/*.lean` | From the conjecture on graphs to left-regular instances (Section 0). |

The theorem: for small `ε, γ > 0` and every
`η > 0`, the gap problem `bkGap ε γ η` (maximum degree `≤ η n`; yes: two disjoint independent sets
of `(1/2 - ε) n` vertices; no: no independent set of `γ n` vertices) is NP-hard.

Source: N. Bansal, S. Khot, *Optimal long code test with one free bit*, FOCS 2009. Their test, as
described by Manurangsi (arXiv:1705.03581, Section 4.2): pick `x ∈ {0,1}^R` and a set `D` of
coordinates, each in `D` with probability `ε_T`; the test accepts if the long codes `f_{v_1}, …,
f_{v_t}` of `t` random neighbours of a random `u` are all constant, with the same value, on the
subcube `C_D(x) = {y : y_j = x_j for j ∉ D}`. Soundness rests on Mossel–O'Donnell–Oleszkiewicz's
"It Ain't Over Till It's Over" [MOO10, Theorem 4.9]. The formalization below is a self-contained
variant of their reduction; the only deviations are choices that make the formal proof shorter.

## Choices that differ from the paper's presentation

* One vertex per random string `(u, k, z, a)`: by folding, the second accepting configuration of
  `(u, k, z, a)` is the first of `(u, k, ¬z, a)`, so the yes-case independent sets are
  `{accepted, z_{σ(u)} = b}`.
* Soundness through the averaged long codes `g_u` and the single-function theorem, with the
  KKMO decoding already formalized for BGHKLMM26, instead of the multi-function form with
  cross-influences (Manurangsi's Theorem 11, from [Svensson 2013]); `t` enters only through the
  `t`-th moment.
* Free coordinates `{j : a_j = 0}` for uniform `a ∈ [M]^R` (density `1/M`), so all vertices have
  the same weight and the graph is unweighted with no replication.
* Self-conflicting vertices (all coordinates free) are discarded in the soundness; that parallel
  constraints agree is used there.
* The instances are left-regular with agreeing parallel constraints, not simple and bi-regular:
  right-regularity is never used, and parallel constraints with the same table are harmless.
  These are the instances that the Unique Games Conjecture on graphs gives after the double cover
  and a regularization (Section 0).
* The left vertices are capped at the number of constraints, so the output has polynomial size
  on every input; `R = 0` (no yes-instances) is handled by a constant map.

## 0. From the conjecture to left-regular instances (`../UG/`)

`BHSV25.UG.lrHard_of_khotUGC : UniqueGames.KhotUGC → BHSV25.BK.LRHard`, for `ε ≤ 1/4`, from the
conjecture at `ε / 4` and `ℓ = ⌈2/ε⌉`:

* **Double cover** (`UG/Cover.lean`): a left and a right copy of every vertex, and for each
  constraint `((u, v), π)` the constraints `((u, v), π)` and `((v, u), π⁻¹)`. It is valid with
  agreeing parallel constraints on simple instances (`u ≠ v`). A labeling of the graph on both
  sides satisfies the same fraction; for a labeling `(σ, τ)` of the cover, labeling each vertex
  from `σ` or `τ` over all `2^n` choices satisfies each constraint for a quarter of the choices
  per satisfied copy, so `val(cover) ≤ 2 val`.
* **Regularization** (`UG/Regular.lean`, Khot and Regev [KR08, Lemmas 3.3 and 3.4] in one step):
  one left vertex per constraint, a copy of its left vertex `x` of degree `d`, with each
  constraint at `x` repeated `⌊A/d⌋` times and the first `A mod d` more times, `A = ℓ |cs|`. The
  copies of `x` (there are `d`) carry its weight, each block is within `d` of `(A/d) F_x(a)`
  satisfied constraints for the label `a`, and the errors sum to at most `|cs|² = |cs| A / ℓ`, so
  the value moves by at most `1/ℓ`; soundness relabels every copy of `x` by a best label for `x`.
* **Polynomial time** (`UG/Machine.lean`), and the assembly (`UG/Bridge.lean`): the gap
  `(1 - ε/4, ε/4)` goes to `(1 - ε/4, ε/2)`, then into `(1 - ε, ε)` on left-regular instances.

## 1. The reduction (`BK/Graph.lean`)

Input: a Unique Games instance `(m, n, R, cs)` (left vertices `u < m`, right `v < n`, constraints
`((u, v), π)`, satisfied when `σ(u) = π(τ(v))`), assumed valid, left-regular, with parallel
constraints agreeing and `R` labels (the promise `BHSV25.BK.Good` of `BHSV25.BK.lrGap`). Parameters: `t` (queries), `M` (free coordinates have
density `1/M`), `k₀` (copies), `s` (clique size for degenerate inputs).

* `L` = number of constraints at `u = 0` (= left degree), `nbrs u` = constraints at `u` (list).
* **Vertices** (`N = m L^t 2^R M^R` of them): `r = (u, k, z, a)` with `u < m`, `k : [t] → [L]`,
  `z ∈ {0,1}^R`, `a : [R] → [M]`; `D = {j : a_j = 0}` is the set of free coordinates. Numbered
  by mixed radix: `x = u + m (K + L^t (Z + 2^R A))`, `K, Z, A` the base-`L`, base-`2`, base-`M`
  numbers of `k, z, a` (Mathlib's `finProdFinEquiv`, `finFunctionFinEquiv`).
* **Demands.** Vertex `r` asks, for each `p < t`, with `c_p = nbrs(u)[k_p] = ((u, v_p), π_p)`:
  `f_{v_p} ≡ 1` on the subcube `{w : w_i = z_{π_p(i)} for i with π_p(i) ∉ D}` of `v_p`'s cube
  (the points `π_p y`, `y ∈ C_D(z)`, where `(π y)_i = y_{π(i)}`). With folded long codes
  (`f(¬w) = ¬f(w)`), "`≡ 0` on `C_D(z)`" is the demand of `(u, k, ¬z, a)`, so one bit is free and
  each random string needs only this one vertex.
* **Edges** (`SimpleGraph.fromRel` of `conflict`): `r, r'` conflict if some `p, p'` have
  `v_p = v'_{p'}` and the two subcubes are incompatible for a folded function, i.e. one meets the
  negation of the other: `z_{π_p(i)} ≠ z'_{π'_{p'}(i)}` for every `i` fixed in both.
* **Copies**: `k₀ = ⌈1/η⌉ + 1` disjoint copies, so the maximum degree (`< N`) is at most
  `η k₀ N`; independence ratios and disjoint independent sets are unchanged.
* **Degenerate inputs** (`L = 0`, which on valid bi-regular instances means no constraints, value
  `0`): `k₀` disjoint copies of the clique `K_s`, `s > 1/γ`, a no-instance.

All counts are polynomial in the input since `t, R, M, k₀` are constants.

## 2. Completeness (`BK/Complete.lean`)

Labeling `(σ, τ)` satisfying `≥ (1 - ε_UG)|cs|` constraints. A vertex is *accepted* if its `t`
constraints are satisfied and `σ(u) ∉ D`. `I_b = {accepted r : z_{σ(u)} = b}`, `b = 0, 1`:
disjoint. Independent: if `r, r' ∈ I_b` conflict through `v`, the coordinate `i = τ(v)` has
`π_p(i) = σ(u)` fixed with `z_{σ(u)} = b`, and the same for `r'`, contradicting incompatibility.
Union bound: `Pr[not accepted] ≤ t ε_UG + 1/M`, and flipping `z_{σ(u)}` shows
`|I_0| = |I_1| = #accepted / 2 ≥ (1 - t ε_UG - 1/M) N / 2 ≥ (1/2 - ε) N`.

## 3. Soundness (`BK/Sound.lean`)

Let `S` be independent with `|S| ≥ γ N` (in one copy).

1. **Self-consistent vertices.** A vertex conflicts with itself only if two of its constraints
   have the same right vertex; parallel constraints agree, so their demands coincide, and all
   coordinates are free: `a = 0`. These are `N / M^R ≤ N / M ≤ γ N / 4` vertices; drop them: `S'`, `|S'| ≥ 3γN/4`.
2. **Folded long codes.** `f_v(w) = 1` if some demand of `S'` at `v` contains `w`; `0` if one
   contains `¬w`; `w_0` otherwise. Independence makes this well defined and folded, and every
   vertex of `S'` *accepts*: `f_{v_p}(π_p y) = 1` for all `p` and `y ∈ C_D(z)`.
3. **Factorization.** `#accepting r = Σ_{u, z, a} (Σ_{k<L} [f_{v_k} ∘ π_k ≡ 1 on C_D(z)])^t`, and
   `[f_v ∘ π ≡ 1 on C_D(z)] ≤ E_{y ∈ C_D(z)} f_v(π y)`. With the averaged long code
   `g_u(w) = E_{k} f_{v_k}(π_k w)` (`avgTable`, mean `1/2` by folding):
   `Pr_r[accept] ≤ E_u E_{z,a} [ (E_{y ∈ C_D(z)} g_u(y))^t ]`.
4. **Analytic theorem** (`BHSV25.BK.ItAintOver`, below): if `g_u` has no coordinate of degree-`K`
   influence `≥ τ` (in `2 g_u - 1`), the inner expectation is `≤ γ/8`.
5. **Decoding** (`BHSV25.BK.few_bad`, copied from BGHKLMM26's `kkmo_few_bad`, KKMO-style): if
   more than `γ m / 8` left vertices have an influential coordinate, convexity of influences and
   `π` moving them give a labeling satisfying `γ τ² / (32 (K+1))` of the constraints; so on
   instances of value `≤ ε_UG ≤ ε₁(K, τ, γ)` at most `γ m / 8` are bad.
6. Hence `3γ/4 ≤ |S'|/N ≤ Pr_r[accept] ≤ γ/8 + γ/8`, a contradiction.

## 4. The analytic theorem (`BK/AintOver.lean`)

`ItAintOver`: for every `M ≥ 2` and `ζ > 0` there are `K`, `τ > 0` and `t` such that for every
`R` and `g : {0,1}^R → [0,1]` with `E g ≤ 1/2` and every degree-`K` influence of `2g - 1` below
`τ`, `E_{z, a} [(E_{y ∈ C_{D(a)}(z)} g(y))^t] ≤ ζ`, where `a : [R] → [M]` uniform and
`D(a) = {j : a_j = 0}`. It follows (`itAintOver_of_prob`) from the probability form
`ItAintOverProb`, [MOO10, Theorem 4.9]: `Pr[E_{C_D(z)} g ≥ 1 - δ] ≤ ζ/2` for low-influence `g`,
and `(1 - δ)^t ≤ ζ/2` for large `t`. Section 7 proves the probability form.

The formal statement (`BHSV25/BK/AintOver.lean`): for `M ≥ 2`, `ζ > 0` there are `δ > 0`, `K`,
`τ > 0` with `E_{z ∈ {0,1}^R} E_{a ∈ [M]^R} [1 - δ ≤ E_{y ∈ {0,1}^R} g(mix a z y)] ≤ ζ` for all
`R` and `g : {0,1}^R → [0,1]` with `E g ≤ 1/2` and `cutoffInfluence K i (2g - 1) < τ` for all `i`
(OpenAI's degree-`K` influences), where `mix a z y` is `y` on `{j : a_j = 0}` and `z` elsewhere.

## 5. Parameters and assembly (`BK/Main.lean`)

`ε₀ = 1/8` (so `γ ≤ 1/2 - ε`). Given `ε, γ ∈ (0, ε₀]`, `η > 0`:
`M = ⌈2/ε⌉ + ⌈4/γ⌉ + 2`; `(K, τ, t)` from `ItAintOver M (γ/8)`; `ε₁` from `few_bad K τ (γ/8)`;
`ε_UG = min(ε₀, ε₁, ε / (2(t+1)))`; `R` from `BHSV25.BK.LRHard` for `ε_UG`. If `R = 0` the
yes-instances of `lrGap 0` are empty (no labeling, value `0`) and the reduction maps everything to
the fixed no-instance. Otherwise the reduction above maps yes to yes (Section 2) and no to no
(Section 3); `NPHard.trans` with the hardness of `lrGap R ε_UG` gives
`NPHard encGraph (bkGap ε γ η)`.

## 6. Polynomial time (`BK/Machine.lean`)

The output is `(k₀ N, table)` with `table = [adj(i / (k₀N), i % (k₀N)) | i < (k₀N)²]`, and the
adjacency of two vertex numbers is computed from their digits by list functions (`List.range`,
`any`, `all`, `getD`, `filter`, binary `/`, `%`, `^` with unary exponents), certified with
complexitylib's calculus as in `BGHKLMM26/Hardness/MachineList.lean`. The permutation entries are
only used as indices into lists of `R` digits (`getD`), never as exponents.

## 7. Proof of `itAintOverProb`

Files `BK/Invariance*.lean`, `BK/Ensemble.lean`, `BK/HyperReverse.lean`, `BK/AintProof.lean`.

Route: invariance between two *discrete* ensembles (no Gaussians, no `[0,1]`-truncation), then
reverse hypercontractivity on the cube. Notation: `ρ = 1 - 1/M`, `r = √ρ`, `k = 2M` (so
`r ≤ 1 - 1/k`), `ĝ` the Walsh coefficients of `g`. Namespace `BHSV25.BK.Aint`.

1. **Subcube averages as a polynomial** (`Ensemble.lean`). `E_y g(mix a z y) = Σ_S ĝ(S) Π_{i∈S}
   [aᵢ ≠ 0] χ(zᵢ) = mlEval (smoothC r ĝ) U` with `Uᵢ = [aᵢ ≠ 0] χ(zᵢ)/r` i.i.d. of law
   `law3 M` (`0` w.p. `1/M`, `±1/r` w.p. `(1-1/M)/2`): mean 0, variance 1, third moment 0,
   fourth moment `1/ρ ≤ 2`, so a `GoodLaw`; and `E_{z,a} f(U) = ∫ f d(law3 M)^{⊗R}`.
2. **Invariance** (`Invariance*.lean`, copied from `BGHKLMM26/RobustMIS/{Defs,Mollify,
   Multilinear,MultilinearGauss,Bonami,Lindeberg,Invariance}.lean`, with the Lindeberg hybrid made
   generic in the two good laws and the influence hypothesis only on degree `≤ n`): for `r < 1`,
   `L`, `ε > 0` there are `n` and `τ > 0` such that for all good laws `ν₁, ν₂`, `Σ c² ≤ 1`,
   `Infᵢ^{≤n}(c) ≤ τ` and `L`-Lipschitz `ψ`:
   `|∫ ψ(mlEval (smoothC r c)) dν₁^{⊗R} - ∫ ψ(mlEval (smoothC r c)) dν₂^{⊗R}| ≤ ε`.
   Applied to `ν₁ = law3 M`, `ν₂ = signLaw`: the second integral is `E_x ψ(T_r g(x))`.
3. **Reverse hypercontractivity on the cube** (`HyperReverse.lean`): for `f, h : {0,1}^n → [0,1]`
   and `0 ≤ r ≤ 1 - 1/k`: `E_x[f(x) T_r h(x)] ≥ (E f)^k (E h)^k`. Induction on `n` (split the
   first coordinate) from the two-point inequality
   `((1+r)(p₁ᵏq₁ᵏ + p₂ᵏq₂ᵏ) + (1-r)(p₁ᵏq₂ᵏ + p₂ᵏq₁ᵏ))/4 ≥ ((p₁+p₂)/2)ᵏ((q₁+q₂)/2)ᵏ`, which follows
   (Aczél) from the one-function form `A² - rD² ≥ ((p₁+p₂)/2)^{2k}` (`A, D` = half sum and half
   difference of `p₁ᵏ, p₂ᵏ`), i.e. `x^{2k} + y^{2k} + (4k-2)(xy)ᵏ ≥ 4k((x+y)/2)^{2k}`, proved by
   monotonicity in `t` along `x = m + t, y = m - t` (derivative `≥ 0` by AM-GM on
   `Σ_{j<2k-1} xʲ y^{2k-2-j} ≥ (2k-1)(xy)^{k-1}`).
   Consequence: for `g ∈ [0,1]` with `E g ≤ 1/2`, `α = P_x[T_r g ≥ 1 - δ']` satisfies
   `α^{k-1} ≤ 2ᵏ δ'` (take `f = 1_A`, `h = 1 - g`: `E[1_A (1 - T_r g)] ≤ δ' α`).
4. **Assembly** (`AintProof.lean`): `δ = (ζ/2)^{k-1}/2^{k+2}`, the ramp `ψ` (`0` below `1 - 2δ`,
   `1` above `1 - δ`, `1/δ`-Lipschitz), `(n, τ)` from step 2 with `ε = ζ/2`, `K = n`, influence
   bound `4τ` (`cutoffInfluence K i (2g-1) = 4 Infᵢ^{≤K}(ĝ)`):
   `P[F ≥ 1-δ] ≤ E ψ(F) ≤ E ψ(T_r g) + ζ/2 ≤ P[T_r g ≥ 1 - 2δ] + ζ/2 ≤ ζ`.
