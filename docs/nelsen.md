# Further standard copula results

Reference: Roger B. Nelsen, *An Introduction to Copulas*, second edition,
Springer, 2006, [publisher page and DOI](https://link.springer.com/book/10.1007/0-387-28678-0).
The following are independently written Lean proofs using the package's
probability-measure representation.

## Coverage map

| Topic in Nelsen | Formal module | Added results |
| --- | --- | --- |
| Exercise 2.8; §3.2.6, conditions (3.2.21) | `Copula.Diagonal` | Diagonal bounds, monotonicity, 2-Lipschitz regularity, endpoint values, and `δ = id ↔ C = M` |
| §3.2.6, order-statistic interpretation | `Copula.Diagonal` | Distribution functions of the coordinate maximum and minimum |
| §2.6 | `Copula.Reflection.Bivariate` | Single-coordinate reflection formulas, survival copula, transpose and composition identities |
| §2.7 | `Copula.Symmetry` | Copula-level exchangeability and radial symmetry, CDF characterizations, mixtures and symmetrization |
| §5.1, symmetry properties of concordance | `Copula.Rank.Symmetry` | Transpose and survival invariance; single-reflection sign changes |
| §5.4, including the CDF formulas of Theorem 5.4.2 | `Copula.TailDependence` | Limits, range, uniqueness, reflection duality, order and mixture results, benchmark/family values |

These are the precise formalized portions, not claims that every theorem in
the cited sections is implemented. The general random-variable versions of
the symmetry characterizations are not part of this addition.

## Diagonals and transformations

`C.diagonal t` is `C.cdf ![t,t]`. The API proves the necessary conditions on
diagonal sections, but does not yet construct a copula from an arbitrary
admissible diagonal. Only the identity diagonal is proved to determine its
copula uniquely; there is no such general uniqueness claim.

`C.transpose` abbreviates coordinate exchange, and `C.survivalCopula` reflects
all coordinates. The existing `C.reflect {0}` and `C.reflect {1}` give the two
single-coordinate reflections. Their CDF formulas apply to singular copulas
as well as copulas with densities: null coordinate boundaries follow from
uniform marginals.

Exchangeable and radially symmetric copulas are closed under convex mixtures.
Equal mixtures with the transpose or survival copula provide two explicit
symmetrization constructions. Benchmarks and FGM satisfy both symmetries;
radial symmetry is also proved for the Fréchet mixture family.

## Rank symmetries

| Operation | rho | tau | footrule | gamma | beta |
| --- | --- | --- | --- | --- | --- |
| Transpose | Unchanged | Unchanged | Unchanged | Unchanged | Unchanged |
| Both coordinates reflected | Unchanged | Unchanged | Unchanged | Unchanged | Unchanged |
| One coordinate reflected | Negated | Negated | No sign rule asserted | Negated | Negated |

The footrule normalization remains the package's `[-1/2,1]` convention.
Chatterjee's xi is directional and is not covered by this table.

## Tail dependence

`HasLowerTailDependence C l` and `HasUpperTailDependence C l` assert both
existence and value of the relevant limit. No coefficient is assigned when
the limit has not been proved to exist.

Both definitions use a positive tail width tending to zero. The upper tail
uses the threshold `1-t`; `hasUpperTailDependence_iff_tendsto_one` proves its
equivalence with the conventional threshold tending to one. The ratios are
defined at zero using Lean's total division, but the limiting filter excludes
that point.

The API proves uniqueness, values in `[0,1]`, invariance under transposition,
exchange of upper and lower tails under full reflection, equality of tails
for radially symmetric copulas when limits exist, monotonicity in concordance
order, and affine behavior under two-component mixtures.

| Copula | Lower tail | Upper tail |
| --- | --- | --- |
| Independence | 0 | 0 |
| Comonotonicity | 1 | 1 |
| Countermonotonicity | 0 | 0 |
| FGM, all admissible parameters | 0 | 0 |
| Fréchet mixture with weight `a` on `M` | `a` | `a` |
| Mardia parameter `θ` | `θ²(1+θ)/2` | `θ²(1+θ)/2` |

Further book topics include prescribed-diagonal constructions, ordinal sums,
shuffles, derivative characterizations, generator formulas for tail dependence,
and tail coefficients for the remaining analytic and elliptical families.
Those results are not asserted here.
