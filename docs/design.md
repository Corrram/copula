# Design review and roadmap

## Representation

The primitive object is a probability measure on `Fin d → unitInterval` with
uniform coordinate marginals. This separates the probability-theoretic object
from the distribution-function characterization and lets downstream proofs
use mathlib's integration, pushforward, and probability-measure APIs directly.
`Copula.measure` retains the bundled `ProbabilityMeasure`, including access to
its existing weak-convergence infrastructure; `Copula.toMeasure` exposes the
underlying measure and its probability instance.

The underlying cube is a function type, so coordinate evaluation is measurable
and lower orthants are simply `Set.Iic u` for the pointwise order. No new cube
notation or multivariate CDF abstraction is needed for the initial API.

`Fin d` is a convenient public dimension convention. Generic measure and
marginal lemmas should use general index types when appropriate for mathlib;
there is no need to generalize the bundled copula type before a concrete use
case or upstream feedback calls for it.

## Refinements to the initial proposal

1. **Keep the CDF derived and real-valued.** The underlying measure already
   exposes `ℝ≥0∞` values. Since its total mass is one, the familiar real-valued
   CDF is safe and its range bounds are proved. A function-first interface and
   its equivalence to measures belong in a later layer.
2. **Make random-vector constructions reusable.** `Copula.ofMap` accepts a
   measurable vector with uniform coordinate laws. It supports dependent
   examples without rebuilding the marginal proof pattern each time.
3. **Generalize permutations to coordinate selection.** `Copula.reindex` accepts
   any map between finite coordinate sets. It includes lower-dimensional
   marginals, permutations, and repeated coordinates. Injectivity is not
   required to preserve uniform marginals.
4. **Keep dimension zero.** Empty products and empty infima are one. A zero
   coordinate cannot exist in dimension zero, so groundedness takes an explicit
   coordinate or a `NeZero d` assumption. Public examples exercise this case.
5. **Pin a release.** Both Lean and mathlib use v4.34.0, with exact dependencies
   recorded by Lake. No mathlib fork is required. The namespace is chosen to
   ease upstreaming, but the final upstream API remains subject to review.
6. **Separate implemented results from research milestones.** There are no
   placeholder `Sklar` or family modules and no axioms standing in for future
   proofs. Add each module when it contains checked mathematics.

## Completed foundation

- Copula definition, extensionality, coordinate laws, and random-vector constructor.
- Derived CDF with nonnegativity, upper bounds, monotonicity, groundedness,
  total mass, and uniform-marginal boundary identities.
- Independence and comonotonic examples, with their classical CDF formulas.
- Coordinate transformations with identity, composition, and inverse laws.
- Fréchet–Hoeffding lower and upper bounds, including the empty dimension.
- The Lipschitz estimate for the sum of coordinate distances; a `d`-Lipschitz
  theorem for the default maximum metric; continuity and uniform continuity.
- CDF extensionality: lower orthants form a generating pi-system, so equality
  of CDFs implies equality of the underlying copula measures.
- Selected-coordinate reflections and the bivariate countermonotonic copula,
  with CDF `max 0 (u + v - 1)` and its relationship to the diagonal copula.
- Rectangle probabilities as alternating CDF sums, the `d`-increasing property,
  and the explicit four-term formula in dimension two.
- The classical boundary and rectangle predicate and its equivalence to
  measure-based copulas in every finite dimension. Rectangle splitting gives
  monotonicity and the sharp Lipschitz estimate without assuming continuity.
  Finite atomic approximations have CDF error at most `d / 2^n`; weak compactness
  and the portmanteau inequalities identify the representing probability measure.
- The continuous probability integral transform, a compact-interval quantile
  with its adjunction, and inverse-transform sampling for laws with atoms.
- General Sklar existence using randomized inverses from disintegration and
  a strictly increasing embedding of real coordinates into the unit interval.
  Uniqueness is proved on marginal CDF ranges in general, and on the entire
  cube for continuous marginals.
- Gaussian copulas for positive semidefinite correlation matrices. Identity
  correlation gives independence, all-ones correlation gives comonotonicity,
  and arbitrary coordinate selection gives the corresponding covariance submatrix.
- Positive-parameter Clayton copulas from gamma frailty, with the gamma Laplace
  transform, joint and marginal distribution formulas, and the explicit copula
  CDF. The CDF converges pointwise to independence as the parameter approaches
  zero from above, and to comonotonicity as it tends to infinity.
- Bivariate Archimedean admissibility from analytic generator conditions, the
  outer-power transformation, and checked Gumbel, Joe, positive Frank, BB1, and
  BB6 families. The generator construction agrees with the existing Clayton
  measure, whose generator is identified in every finite dimension.
- Max-stability and its preservation under coordinatewise power products;
  Marshall–Olkin, Cuadras–Augé, common-shock, and asymmetric logistic copulas.
- Gaussian scale mixtures with proved atomless marginals and Sklar
  factorization: Student-t, Cauchy, variance-gamma, Laplace, slash, and
  normal–lognormal constructions, including singular dispersion matrices.
- Finite mixtures, FGM with both parameter signs, Fréchet mixtures, and Mardia.
  See [the family catalogue](families.md) for precise coverage and parameter ranges.
- Six population rank dependence coefficients with sharp ranges and benchmark
  values. The xi definition uses conditional kernels, supports singular laws,
  and has a proved conditional-variance formula and functional-dependence
  implication. Spearman's rho has both moment and CDF integral formulas;
  rho, footrule, gamma and beta have mixture identities and exact FGM values.
  See [rank coefficients](rank-coefficients.md) for conventions and remaining work.

## Remaining mathematical milestones

1. **Further analytic family results:** Gaussian formulas using normal quantiles
   and a higher-dimensional admissibility theorem for Archimedean generators.
   Bivariate convexity and the outer-power construction are already proved.
   The Clayton constructor covers `θ > 0`; negative parameters need a separate
   construction with dimension-dependent admissibility.
2. **Further transformation identities:** reflection CDF formulas for arbitrary
   copulas and interactions with coordinate selection.
3. **Topology of copulas:** connect pointwise CDF convergence to uniform CDF
   convergence and weak convergence of the bundled probability measures.

## Classical measure construction

The converse proof uses finite atomic approximations rather than a new general
multivariate measure-extension API. Repeated binary cuts split rectangle
increments additively. Their nonnegative weights sum to one, so placing each
weight at the rectangle's upper corner gives a probability measure. Clipping
rectangles against a lower orthant bounds its CDF between the classical
function at the requested point and at a point shifted down by the mesh width.
The derived Lipschitz estimate gives a uniform error bound of `d / 2^n`.

Probability measures on the compact cube have a weakly convergent subsequence.
The closed-set portmanteau inequality supplies one CDF bound. Slightly enlarged
open orthants supply the other, including on the upper boundary. This identifies
the limit's CDF with the original function. `IsClassical.ofMeasure` then identifies
its uniform marginals, and CDF extensionality gives uniqueness.

## General Sklar construction

The general existence proof does not require the classical function-to-measure
converse. It starts from an existing joint probability law. Its one-dimensional
quantile maps sample the coordinate laws from uniform variables. Conditional
distributions and mathlib's kernel representation theorem supply randomized
inverses of those maps. Lifting the joint law through these inverses produces a
copula, and the quantile adjunction proves the CDF factorization. A strictly
increasing sigmoid embedding transfers the construction from the compact unit
cube to arbitrary real-vector laws. The continuous-marginal construction remains
available separately as the direct marginal-CDF transform.

## Upstreaming and discussion

Propose small contributions: generic missing lemmas (if encountered), then
`Mathlib.Probability.Copula.Basic`, examples, CDF results, and later Sklar
infrastructure. Remove local copies after they land and become available in
the pinned dependency. Avoid treating a planned upstream module name as a
commitment from mathlib maintainers.

A concrete opening question for a public design discussion is:

> I am developing finite-dimensional copulas as a
> `ProbabilityMeasure (Fin d → unitInterval)` with uniform coordinate
> pushforwards. The CDF is derived from lower-orthant probabilities. The
> initial implementation includes product and diagonal examples and coordinate
> selection. Is this representation and namespace a suitable starting point
> for mathlib, and are there existing coupling APIs it should share?

Keep links to actual discussions and review decisions in issues as they occur.

## References

- [Probability measures in mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.html)
- [Uniform volume on the unit interval](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/UnitInterval.html)
- [Finite product measures](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Pi.html)
- [The existing CDF API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/CDF.html)
- [Using mathlib as a dependency](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)

The links above track current documentation. Consult the pinned source in
`.lake/packages/mathlib` for the exact API used by this repository.
