# Positive dependence

Import `Copula.Dependence` or `Copula`. The library separates directional
tail and stochastic properties from total positivity of a CDF, a conditional
kernel, or a density. These objects need different predicates.

## Conventions and definitions

For a bivariate copula, write `(U,V)` for coordinates `(0,1)`. **LTD, RTI and
SI describe V given U.** Apply the predicate to `C.reindex ![1,0]` for the
opposite direction. No symmetry is assumed for these three properties.

| Predicate | Mathematical condition |
| --- | --- |
| `C.IsPQD` | `C(u,v) ≥ uv` (positive quadrant dependence) |
| `C.IsNQD` | `C(u,v) ≤ uv` (negative quadrant dependence) |
| `C.IsLTD` | `u ↦ C(u,v)/u` is nonincreasing for `u > 0` |
| `C.IsRTI` | `u ↦ (1−u−v+C(u,v))/(1−u)` is nondecreasing for `u < 1` |
| `C.IsSI` | Each section `u ↦ C(u,v)` is concave |
| `C.IsSD` | Each section `u ↦ C(u,v)` is convex |
| `C.IsCI` | SI for both `C` and `C.transpose` |
| `C.IsCD` | SD for both `C` and `C.transpose` |
| `C.IsTP2CDF` | `C(a,c) C(b,d) ≥ C(a,d) C(b,c)` for `a ≤ b`, `c ≤ d` |
| `C.HasTP2Kernel` | Some version of the conditional CDF kernel is TP2 |
| `C.HasMTP2Density` | Some nonnegative measurable density version satisfies the MTP2 lattice inequality |

The tail predicates use cross-multiplied inequalities internally, including
the boundary points. Their equivalence to the ratio formulations is proved
by `isLTD_iff_ratio_antitone` and `isRTI_iff_survivalRatio_monotone`.
`isRTI_iff_ratio_antitone` gives the equivalent decrease of
`P(V ≤ v | U > u) = (v−C(u,v))/(1−u)`.

SI uses the chord condition

```text
(b−a) C(c,v) + (c−b) C(a,v) ≤ (c−a) C(b,v),  a ≤ b ≤ c.
```

This is the CDF-section concavity characterization of stochastic increasingness.
It handles coincident endpoints without division. The kernel criterion below
connects this representation to conditional stochastic ordering.

`Dependence.ConditionalMonotonicity` uses the CI/CD convention of Ansari–Rockel.
It proves SD implies NQD and that reflecting the second coordinate interchanges
SI and SD. For exchangeable copulas, CI is equivalent to SI and CD to SD.
All bivariate Archimedean copulas are proved exchangeable. Independence is both
CI and CD, the upper Fréchet bound is CI, and the lower bound is CD. FGM is CI
exactly for nonnegative parameters and CD exactly for nonpositive parameters.
The full Nelsen 7 family is CD.

For background on the distinctions between CDF, kernel and density total
positivity, see [Fuchs and Tschimpke, Total positivity of copulas from a Markov
kernel perspective](https://arxiv.org/abs/2205.01914). The standard tail and
concavity formulations are also discussed in [Weak Dependence Notions and
Their Mutual Relationships](https://www.mdpi.com/2227-7390/9/1/81).

## Proved implications and closure

```text
HasTP2Kernel ──→ IsSI ──→ IsLTD ──→ IsPQD
                   └──→ IsRTI ──→ IsPQD
IsTP2CDF ───────────────→ IsLTD ──→ IsPQD
```

CDF-TP2 also implies LTD after swapping the coordinates. PQD and CDF-TP2
are proved invariant under that swap. The library does not assert such an
invariance for directional SI, LTD or RTI.

SI, LTD, RTI and PQD are each preserved by `Copula.mix`. Total positivity is
not included in this mixture closure result. PQD and NQD together characterize
independence.

Binary [ordinal sums](ordinal-sums.md) also preserve PQD. Every ordinal sum
with an interior split has `C(a,a)=a`, so it fails NQD and differs from
independence, even when both input copulas are independent. The ordinal-sum
module does not yet establish closure of SI, LTD, RTI or total positivity.

```lean
import Copula.Dependence

open ProbabilityTheory
open scoped unitInterval

example (C : Copula 2) (h : C.IsSI) : C.IsPQD := h.isPQD

example (C D : Copula 2) (hC : C.IsSI) (hD : D.IsSI) (a : I) :
    (Copula.mix C D a).IsSI := hC.mix hD a

example (C : Copula 2) (h : C.HasTP2Kernel) : C.IsRTI := h.isSI.isRTI
```

## Conditional kernels and null sets

`cdf_eq_integral_conditionalCDF` proves the disintegration formula

```text
C(u,v) = ∫[0,u] K(t,[0,v]) dt.
```

`cdf_eq_integral_kernel` allows any almost-everywhere equal kernel version.
`isSI_of_kernel` then proves SI when `u ↦ K(u,[0,v])` is antitone for every
`v`. Its proof uses the concavity of the indefinite integral of an antitone
function, rather than derivatives of the copula.

`HasTP2Kernel` quantifies over a Markov kernel that agrees almost everywhere
with `C.conditionalKernel`. It does not require the arbitrarily chosen canonical
kernel to obey an ordering on null conditioning events. The converse construction
of a monotone kernel from the SI chord predicate is not yet formalized.

## Multivariate total positivity and densities

The generic `ProbabilityTheory.IsMTP2 f` expresses

```text
f(x) f(y) ≤ f(x ∧ y) f(x ∨ y).
```

Here the meet and join are coordinatewise minimum and maximum on a cube.
The generic predicate contains the algebraic inequality; nonnegativity is
an explicit, mandatory part of `HasMTP2Density`. This density predicate works
in every finite dimension, including zero, and requires equality of the actual
copula measure with `volume.withDensity (ENNReal.ofReal ∘ f)`.

The library proves the following reusable function results:

- Nonnegative pointwise products preserve TP2 and MTP2.
- Composition with a lattice homomorphism preserves MTP2.
- Products of one-coordinate factors satisfy the lattice identity with equality.
- In dimension two, the lattice and ordered-rectangle inequalities are equivalent.

The density witness implies absolute continuity. The constructor criterion
`toMeasure_eq_withDensity_of_cdf_integral` identifies a density from its
lower-orthant integrals. It is used to identify the FGM density with the existing
FGM copula, so the family result concerns the bundled probability law.

This API uses **density MTP2**. Generalized MTP2 notions for probability measures
that may be singular are a separate extension; see [Positive Dependence and Weak
Convergence](https://www.cambridge.org/core/journals/journal-of-applied-probability/article/positive-dependence-and-weak-convergence/263F19F9852B178BA5D57892457B1ADC).

## Benchmarks and FGM

| Copula | Proved results |
| --- | --- |
| Independence | PQD, NQD, LTD, RTI, SI, CDF-TP2, kernel-TP2; MTP2 density in every dimension |
| Comonotonicity | PQD, LTD, RTI, SI, CDF-TP2, kernel-TP2; no Lebesgue MTP2 density |
| Countermonotonicity | NQD; fails PQD, LTD, RTI, SI, CDF-TP2 and kernel-TP2 |
| FGM, `theta ∈ [-1,1]` | PQD, LTD, RTI, SI and CDF-TP2 each hold exactly when `theta ≥ 0` |

For FGM the density is proved to be

```text
c_theta(u,v) = 1 + theta (1−2u)(1−2v).
```

It is nonnegative for the full admissible parameter interval. The displayed
density satisfies the MTP2 inequality exactly for `theta ≥ 0`; consequently
`hasMTP2Density_fgm` constructs the density witness for every nonnegative
admissible parameter. No claim about conditional-kernel TP2 for FGM is currently
included.

The comonotonic example is an explicit distinction between kernel and density
total positivity: its diagonal has full copula mass and zero cube volume.

## Rank consequences and remaining work

PQD implies nonnegative Spearman rho, Kendall tau, Spearman footrule, Gini gamma
and Blomqvist beta. It also implies `rho ≤ 3 tau`. The implication chains above
let SI, LTD, RTI and CDF/kernel TP2 hypotheses supply these conclusions. Xi is
already nonnegative for every copula, so its sign does not characterize positive
dependence.

Import `Copula.Order.StrictSpearman` (or `Copula`) for the sharpened criteria:
within PQD, rho and tau are positive exactly when the copula differs from
independence, and either coefficient being zero forces independence. Within
NQD the analogous signs are negative, and zero again forces independence.
The NQD proof also supplies `3 tau ≤ rho ≤ 0`. These equivalences rely on the
quadrant-dependence hypothesis; they do not hold for arbitrary copulas.

The generic implications from density MTP2 to kernel/CDF TP2, association and
FKG inequalities, a monotone-kernel converse for SI, and further family
classifications remain future work. They are not hidden assumptions of any
current theorem.

## Module map

- `Dependence.Basic`: quadrant, tail and SI predicates, ratio equivalences and mixture closure.
- `Dependence.TotalPositivity`: generic TP2/MTP2 algebra, CDF and density predicates.
- `Dependence.Conditional`: disintegration, the conditional SI criterion and kernel TP2.
- `Dependence.Transpose`: swapping coordinates and symmetric predicates.
- `Dependence.Rank`: signs of rank coefficients and the `rho ≤ 3 tau` bound.
- `Dependence.Examples`, `Singular`: benchmark memberships, failures and the singular-density distinction.
- `Dependence.Density`, `FGM`, `FGMDensity`: density identification and exact FGM results.
