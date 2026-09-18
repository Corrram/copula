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

## Next mathematical milestones

1. **CDF regularity:** Lipschitz continuity, rectangle increments, the
   `d`-increasing property, and the full Fréchet–Hoeffding bounds.
2. **Further examples:** bivariate countermonotonicity and coordinate reflections;
   uniqueness in dimensions zero and one; relationships between the examples
   and existing independence APIs.
3. **Classical characterization:** define a function-level predicate with the
   exact boundary and rectangle conditions, construct the associated measure,
   and prove equivalence with `Copula d`. Do not silently assume continuity or
   countable additivity in the converse direction.
4. **Sklar infrastructure:** laws on `Fin d → ℝ`, marginal CDFs and quantiles,
   and the probability integral transform. Reuse generic mathlib results where
   possible and upstream missing distribution lemmas separately.
5. **Sklar's theorem:** distinguish existence for arbitrary marginals from
   uniqueness for continuous marginals. In the discontinuous case, uniqueness
   is only on the product of marginal CDF ranges. A naive deterministic CDF
   transform does not give uniform marginals when atoms are present; the proof
   needs an appropriate extension or randomized distributional transform.
6. **Parametric families:** Gaussian and Archimedean constructions after the
   foundational results are stable. Keep statistical and research-specific
   APIs separate from the initial upstream contribution.

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
