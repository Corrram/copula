# lean-copula

[![Lean](https://github.com/Corrram/lean-copula/actions/workflows/lean.yml/badge.svg)](https://github.com/Corrram/lean-copula/actions/workflows/lean.yml)

Finite-dimensional copulas in Lean 4, built on mathlib. This is an independent,
early-stage project intended for research use and eventual upstream contributions.
The API is still open to feedback.

## Design

A `ProbabilityTheory.Copula d` is a probability measure on
`Fin d → unitInterval` with uniform coordinate marginals. Its distribution
function is derived as the real-valued probability of a lower orthant:

```lean
import Copula

open ProbabilityTheory
open scoped unitInterval

example (C : Copula 2) : C.cdf (fun _ => 1) = 1 := C.cdf_one

example (C : Copula 2) (u : Fin 2 → I) : 0 ≤ C.cdf u := C.cdf_nonneg u

example (C : Copula 2) (u : I) :
    C.cdf (Function.update (fun _ => 1) 0 u) = (u : ℝ) := by simp
```

This representation uses mathlib's probability measures, uniform volume on the
unit interval, products, and pushforwards. Dimension zero is supported: its CDF
is one, and groundedness is only asserted when a coordinate exists.

## What is implemented

| Module | Contents |
| --- | --- |
| `Copula.Basic` | Definition, measure accessor, extensionality, uniform marginals, construction from a random vector |
| `Copula.CDF` | Real-valued CDF, bounds, monotonicity, groundedness, boundary and marginal identities |
| `Copula.CDF.Bounds` | Fréchet–Hoeffding lower and upper bounds, including dimension zero |
| `Copula.CDF.Continuity` | The sum-distance Lipschitz estimate, continuity, and uniform continuity |
| `Copula.CDF.Extensionality` | Equality of copulas from equality of their CDFs |
| `Copula.Independence` | Product copula and the product formula for its CDF |
| `Copula.Comonotonic` | Diagonal copula and the minimum-coordinate formula for its CDF |
| `Copula.Transform` | Coordinate selection, repetition, and permutation, with composition and inverse laws |
| `Copula.Reflection` | Selected-coordinate reflections, involution, and injectivity |
| `Copula.Countermonotonic` | The bivariate reflected diagonal law and its lower-bound CDF |
| `Copula.Unique` | Uniqueness of copulas in dimensions zero and one |
| `Copula.Rectangle` | Alternating CDF sums, rectangle probabilities, and the increasing property |
| `Copula.Classical` | Equivalence of the classical conditions and measure-based copulas in every finite dimension; `ofClassical` constructor |
| `Copula.Classical.Regularity` | Rectangle splitting, monotonicity, and Lipschitz continuity derived from the classical conditions |
| `Copula.Classical.Approximation` | Finite atomic approximations with CDF error at most `d / 2^n` |
| `Copula.Distribution.ProbabilityIntegralTransform` | Uniformity of continuous CDF transforms and continuity for atomless laws |
| `Copula.Distribution.Quantile` | Quantile adjunction and inverse-transform sampling, including atoms |
| `Copula.Distribution.RandomizedInverse` | Randomized inverses obtained by disintegration |
| `Copula.Distribution.GammaLaplace` | Exponential tilting and the rate-one gamma Laplace transform |
| `Copula.Sklar` | General Sklar existence, uniqueness on marginal ranges, and full uniqueness for continuous marginals |
| `Copula.Families.Gaussian` | Gaussian copulas from positive semidefinite correlation matrices, including singular matrices |
| `Copula.Families.Gaussian.Identities` | Identity correlation gives independence; all-ones correlation gives comonotonicity; coordinate selection corresponds to submatrices |
| `Copula.Families.Clayton` | Positive-parameter gamma-frailty construction with atomless marginals and Sklar factorization |
| `Copula.Families.Clayton.CDF` | Joint frailty tails, explicit marginal CDFs, and the classical Clayton CDF formula |
| `Copula.Families.Clayton.Limits` | Pointwise CDF convergence to independence at zero and comonotonicity at infinity |

Import `Copula` for the full library or a specific module such as
`Copula.Basic`. Declarations live in `ProbabilityTheory.Copula`; the structure
itself is `ProbabilityTheory.Copula`.

The CDF is 1-Lipschitz for the sum of coordinate distances. Lean's default
metric on `Fin d → unitInterval` is the maximum metric; the theorem
`Copula.lipschitzWith_cdf` uses constant `d` for that metric.

`IsClassical.existsUnique` proves the full classical characterization, including
dimension zero. `Copula.ofClassical F hF` constructs its unique representing
copula, and `Copula.cdf_ofClassical` recovers `F`. Continuity follows from the
boundary and rectangle conditions. The measure construction uses finite atomic
approximations and weak compactness on the unit cube.

For `θ > 0` and positive coordinates, `Copula.cdf_clayton` proves

```text
Cθ(u) = (∑ i, uᵢ^(-θ) - d + 1)^(-1/θ).
```

A zero coordinate makes the CDF zero. `tendsto_clayton_zero` and
`tendsto_clayton_atTop` give pointwise CDF limits along any filter of positive
parameters. The package does not yet cover negative Clayton parameters or
general Archimedean generator admissibility.
See [the design review and roadmap](docs/design.md).

## Sklar's theorem

For a real-vector probability law `μ`, `Copula.exists_sklarCopula μ` gives a
copula whose CDF composed with the marginal CDFs equals the joint CDF.
This includes atomic and singular laws. The construction uses quantile maps
and randomized inverses, so atoms are handled without assuming the ordinary
CDF transform is uniform.

`Copula.existsUnique_sklarCopula_of_continuous μ hc` gives full uniqueness
when all marginal CDFs are continuous. Strict monotonicity is not required.
Without continuity, `Copula.IsSklarCopula.cdf_eq_on_ranges` asserts equality
on the product of marginal CDF ranges.

## Build

Install [Lean and elan](https://leanprover-community.github.io/get_started.html),
then run:

```sh
git clone https://github.com/Corrram/lean-copula.git
cd lean-copula
lake exe cache get
lake build
lake test
```

The project pins Lean and mathlib to **v4.34.0**. Commit `lake-manifest.json`
when updating dependencies; it fixes the exact transitive revisions. CI builds
both the library and public API examples, with warnings treated as errors.

## Use in another Lean project

Use the same Lean toolchain and add this to your `lakefile.toml`:

```toml
[[require]]
name = "copula"
git = "https://github.com/Corrram/lean-copula.git"
rev = "main"
```

Run `lake update`, then `import Copula.Basic` or `import Copula`. For
reproducible research, replace `main` with the full commit SHA you used and
commit your dependency manifest. If you also declare mathlib directly, use
the same mathlib revision as this package.

The GitHub repository is `lean-copula`, the Lake package is `copula`, and the
Lean module root is `Copula`.

## Feedback and citation

Design questions, API suggestions, and small contributions are welcome through
[GitHub issues](https://github.com/Corrram/lean-copula/issues) and pull requests.
See [CONTRIBUTING.md](CONTRIBUTING.md) for the upstreaming workflow. When linking
from Zulip or a GitHub discussion, prefer a permalink to the relevant commit and
definition. For research citations, use [CITATION.cff](CITATION.cff) and include
the commit SHA; there is no archived release or DOI yet.

Licensed under [Apache 2.0](LICENSE).
