# Draft modules: uncompiled additions (September 2026)

These modules were written **without access to a Lean toolchain** (the
sandbox could not reach the mathlib cache), then desk-checked twice against
the pinned mathlib v4.34.0 sources. Treat them as untested. They live behind
`Copula.Draft`, which `Copula.lean` does not import, so `lake build` is
unchanged.

```sh
lake exe cache get
lake build Copula.Draft      # builds only the draft modules
```

Fix errors module by module. When `Copula.Draft` builds, add its imports to
`Copula.lean`, delete `Copula/Draft.lean`, and add rows to the README table.
No `sorry`, `admit` or axioms are used anywhere in the draft.

## What is new

| Module | Nelsen | Main results |
| --- | --- | --- |
| `Copula.Topology.Uniform` | §2.10 | Copula CDFs are uniformly equicontinuous (`|F u - F v| ≤ d·dist u v`); pointwise convergence of CDFs along any filter is uniform (`tendstoUniformly_cdf_of_tendsto`, `tendstoUniformly_cdf_iff`) |
| `Copula.Topology.Closed` | §2.10 | Pointwise limits of classical functions and of copula CDFs are again copula CDFs; the classical set is closed and compact (Arzelà–Ascoli); every sequence has a uniformly convergent subsequence (`exists_subseq_tendstoUniformly_cdf`) |
| `Copula.Diagonal.Construction` | §3.2.6 | `IsDiagonalFunction δ` (the necessary diagonal conditions) is also sufficient: `diagKernel`, `diagonalCopula`, `diagonal_diagonalCopula`, `isDiagonalFunction_iff_exists_copula` |
| `Copula.Archimedean.Theory`, `TheoryConvex` | §4.1 | `C(u,v) < min(u,v)` for strict generators; inverse-generator monotonicity lemmas; reusable convexity lemmas for `z^p`, `c/f`, `log(s+c)` |
| `Copula.Archimedean.Diagonal` | §4.1 | Diagonal `δ(t) = ψ(2 φ(t))` and `δ(t) < t` for strict generators |
| `Copula.Families.NelsenTable.N9, N10, N13, N19, N20` | Table 4.1 | Gumbel–Barnett (#9), #10, #13, #19, #20 with generators, CDFs, full-boundary CDF formulas. See `docs/nelsen-table-4-1.md` for the status of all 22 families |
| `Copula.Measures.Deviation` | §5.3 | Shared scaffolding for `∫ φ(C − Π)`: continuity, integrability, transpose/survival invariance, vanishing forces `C = Π`, `ρ = 12∫(C−Π)` |
| `Copula.Measures.SchweizerWolff` | §5.3 | `σ ≥ 0`, `σ(Π)=0`, `σ(M)=σ(W)=1`, `|ρ| ≤ σ`, transpose/survival invariance, `σ = |ρ|` under PQD/NQD, `σ = 0 ↔ C = Π`, FGM: `σ = |θ|/3` |
| `Copula.Measures.Hoeffding` | §5.3 | Hoeffding's `Φ²`: nonnegativity, `Φ²(Π)=0`, invariances, `Φ² = 0 ↔ C = Π`, FGM: `θ²/10` |
| `Copula.RandomVariable.Invariance` | Thm 2.4.3–2.4.4 | Sklar copula under coordinatewise strictly monotone maps (unchanged / reflected / survival), any dimension |
| `Copula.RandomVariable.Independence` | Thm 2.4.2 | Sklar copula is `Π` iff the law is the product of its marginals |
| `Copula.RandomVariable.Monotone` | Thm 2.5.4 | `Y = g(X)` a.s. with `g` strictly monotone gives `M` / `W`; a.s. criteria in terms of the marginal CDFs |
| `Copula.RandomVariable.Symmetry` | §2.7 | Exchangeable / radially symmetric random vectors and their copulas, both directions |
| `Copula.RandomVariable.Ext` | | Equality of laws on `Fin d → ℝ` from lower-orthant probabilities |

## Not proved (needs a compiler or more work)

- `σ ≤ 1` and `Φ² ≤ 1`, `Φ²(M) = 1`. The pointwise bound `|C−Π| ≤ min(u,v)−uv`
  is false (take `C = W`), so these need the genuine Schweizer–Wolff
  argument and the piecewise integral `∫(M−Π)² = 1/90`.
- Converse of Nelsen 2.5.4 (`C = M` implies `Y = f(X)` a.s.), which needs a
  quantile construction of `f`.
- Table 4.1 families #11, #16, #17, #18, #21, #22, and #13 for `0 < θ < 1`.
- Associativity of Archimedean copulas, `δ'(1)` results, Kendall's tau and
  the Kendall distribution function in terms of the generator.
- Markov (`*`) product, Nelsen Chapter 6 material, prescribed-diagonal
  uniqueness results, general ordinal sums with residual comonotone part.

## Highest-risk spots to look at first

`Topology/Closed.lean` (definitional unfolding of `classicalSet`, `arzela_ascoli₂`
unification), `Topology/Uniform.lean` (`UniformFun` unfolding at the end of
`tendstoUniformly_cdf_of_tendsto`), `RandomVariable/Invariance.lean` and
`Symmetry.lean` (defeq-heavy `show`/`funext` steps), `Families/NelsenTable/N9.lean`
(`HasDerivAt` type ascriptions and `convexOn_of_hasDerivWithinAt2_nonneg` argument
names), and `Diagonal/Construction.lean` (`posPart_add_le`).

## Efficiency and clarity audit (no code changed)

Because nothing could be compiled, existing verified code was **not**
refactored. Findings for a later, compiler-backed pass:

1. **Duplicated `Support` modules.** Under `Copula/Rank/Region/` (`XiRho`,
   `XiBlest`, `XiBeta`, `TauFootruleBeta`, `MeanVariance`) there are 26
   files, about 2,900 lines, that are byte-identical to another copy up to the
   paper name in the namespace and import lines (19 distinct modules such as
   `Shuffle`, `CenteredProperties`, `StochasticRho`, `RampIntegrals`,
   `Functional`, `Mixture`). Moving each into a shared
   `Copula/Rank/Region/Common/` namespace and re-exporting would cut build
   time and review surface. Do this with the compiler at hand, one module
   at a time.
2. **Draft aggregator.** Once verified, merge `Copula.Draft` into
   `Copula.lean` (whose import list is unordered by topic; grouping it by
   README table order would help navigation).
3. **Family pattern.** Every family repeats the same four-file shape
   (`Families/X`, `XLimits`, `Dependence/X`, `TailDependence/X`, sometimes
   `Order/X`, `Rank/X`). A generic `BivariateGenerator`-level theorem for
   limits and total positivity (`Dependence.BB1TotalPositivity` already does
   this for log-convex inverse generators) would shrink each new family to
   its generator plus a few instances.
