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

Import `Copula` for the full library or a specific module such as
`Copula.Basic`. Declarations live in `ProbabilityTheory.Copula`; the structure
itself is `ProbabilityTheory.Copula`.

The CDF is 1-Lipschitz for the sum of coordinate distances. Lean's default
metric on `Fin d → unitInterval` is the maximum metric; the theorem
`Copula.lipschitzWith_cdf` uses constant `d` for that metric.

Sklar's theorem, the converse construction from a classical copula function,
and parametric families are planned work. See [the design review and roadmap](docs/design.md).

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
