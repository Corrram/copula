# Ordinal sums

Import `Copula.OrdinalSum` or `Copula`. For bivariate copulas `C`, `D` and
`a : unitInterval`, `C.ordinalSum D a` places C on the square `[0,a]²` and D
on `[a,1]²`. The parameter is the length of the lower interval. The result
is a bundled copula with proved uniform marginals.

This implements the binary construction from Nelsen, *An Introduction to
Copulas*, second edition, §3.2.2 ([book and DOI](https://link.springer.com/book/10.1007/0-387-28678-0)).
All proofs are written independently using the package's classical-to-measure
representation theorem. Both singular and absolutely continuous inputs are
allowed.

## CDF and endpoints

For `0<a<1`, writing `O=C.ordinalSum D a`, the usual formulas are:

```text
O(u,v) = a C(u/a,v/a)                         if u,v ≤ a
O(u,v) = a+(1−a) D((u−a)/(1−a),(v−a)/(1−a))  if u,v ≥ a
O(u,v) = min(u,v)                            on the two other rectangles.
```

The formulas agree at shared boundaries. The implementation uses clipped
rescaling maps `OrdinalSum.lowerCoord` and `OrdinalSum.upperCoord` so that
the constructor also supports `a=0` and `a=1`. The endpoint identities are
`ordinalSum_zero : C.ordinalSum D 0 = D` and
`ordinalSum_one : C.ordinalSum D 1 = C`.

`cdf_ordinalSum_lower`, `cdf_ordinalSum_upper`,
`cdf_ordinalSum_lower_upper`, and `cdf_ordinalSum_upper_lower` give the four
regions. `cdf_ordinalSum_lowerEmbed` and `cdf_ordinalSum_upperEmbed` give
the equivalent affine-coordinate formulas, convenient for rewriting:

```text
O(a u,a v) = a C(u,v)                         when a>0
O(a+(1−a)u,a+(1−a)v) = a+(1−a) D(u,v)       when a<1.
```

At every split, `O(a,a)=a`. For an interior split this proves that O is
dependent and fails negative quadrant dependence, regardless of the two
components. In particular, two independent components still yield a dependent
copula. Splitting at `a=1/2` gives CDF values `1/8` at `(1/4,1/4)`, `5/8` at
`(3/4,3/4)`, and `1/4` at `(1/4,3/4)`.

## Recovery, order and positive dependence

At a fixed interior split, `ordinalSum_eq_iff` recovers both components:

```text
ordinalSum(C,D,a) = ordinalSum(E,F,a) ↔ C=E and D=F.
```

`lowerOrthantLE_ordinalSum_iff` likewise gives the exact comparison:

```text
ordinalSum(C,D,a) ≤lo ordinalSum(E,F,a) ↔ C≤lo E and D≤lo F.
```

The forward construction preserves lower orthant order at all split points,
including the endpoints. The recovery implications require both block lengths
to be positive. In dimension two the same comparison also determines
concordance and upper orthant order through the existing equivalences.

`IsPQD.ordinalSum` proves closure of positive quadrant dependence. No converse
or closure under SI, LTD, RTI or total positivity is claimed here.

## Probability law and integration

`OrdinalSum.Measure` identifies the underlying measure directly. Write
`L_a(x)_i = a x_i` and `U_a(x)_i = a+(1−a)x_i`. Then

```text
μ_(C⊕ₐD) = a (L_a)_* μ_C + (1−a) (U_a)_* μ_D.
```

`toMeasure_ordinalSum` states this identity using `Measure.map` and
nonnegative extended-real weights. `integral_ordinalSum` gives the resulting
change-of-variables formula for every continuous real observable:

```text
∫ f d(C⊕ₐD) = a ∫ f(L_a(x)) dC(x) + (1−a) ∫ f(U_a(x)) dD(x).
```

Both formulas include `a=0` and `a=1`; neither needs a density.
`OrdinalSum.Blocks` proves that the lower square has probability a, the upper
square has probability 1−a, and the two off-diagonal open rectangles have
probability zero. The block indicators of the two coordinates agree almost
surely. Closed block boundaries do not change their probabilities because
uniform marginals have no atoms.

## Rank coefficients and sharp bounds

For any components C and D and every split a, `OrdinalSum.Rank` proves:

```text
rho(C⊕ₐD) = 1 − a³(1−rho(C)) − (1−a)³(1−rho(D))
tau(C⊕ₐD) = 1 − a²(1−tau(C)) − (1−a)²(1−tau(D))
footrule(C⊕ₐD) = 1 − a²(1−footrule(C)) − (1−a)²(1−footrule(D)).
```

The more general concordance identity requires a common split for both inputs:

```text
Q(C⊕ₐD, E⊕ₐF) = 1 − a²(1−Q(C,E)) − (1−a)²(1−Q(D,F)).
```

Tau follows by pairing the copula with itself; footrule follows by pairing
with M, which is an ordinal sum of two copies of itself. Rho follows from
the squared difference of the two uniform coordinates. These proofs include
singular components and zero-length blocks.

`OrdinalSum.RankExamples` specializes the formulas:

| Components | rho | tau | footrule |
| --- | --- | --- | --- |
| Π, Π | `3a(1−a)` | `2a(1−a)` | `2a(1−a)` |
| W, W | `6a(1−a)−1` | `4a(1−a)−1` | `3a(1−a)−1/2` |

The W/W row gives sharp lower bounds over all component choices at a fixed
split. In particular, every ordinal sum at `a=1/2` has rho at least 1/2,
tau at least 0, and footrule at least 1/4. W/W attains all three bounds,
giving a dependent copula with zero tau and positive rho; it is not PQD.

For Π/Π, the respective maxima are 3/4, 1/2 and 1/2. The library proves that
each maximum is attained exactly at `a=1/2`. Equal splitting therefore
maximizes these three coefficients within this particular family.

## Symmetry and extremal copulas

Transposition acts on both components:
`(C.ordinalSum D a).transpose = C.transpose.ordinalSum D.transpose a`.
Exchangeable inputs therefore give an exchangeable ordinal sum; at an interior
split the converse holds as well.

An ordinal sum of two copies of M is M. At an interior split, the sum equals
M exactly when both components are M. These statements do not assert
uniqueness of the split point.

## Tail dependence

The proved equivalences include both existence and value of the limits:

```text
HasLowerTailDependence (ordinalSum C D a) l ↔ HasLowerTailDependence C l   if a>0
HasUpperTailDependence (ordinalSum C D a) l ↔ HasUpperTailDependence D l   if a<1.
```

The proof rescales the tail width and compares the ratios near zero. It
requires no density, derivatives, or symmetry. For every interior split:

| Lower component | Upper component | Lower tail | Upper tail |
| --- | --- | ---: | ---: |
| M | Π | 1 | 0 |
| Π | M | 0 | 1 |
| W | W | 0 | 0 |
| Π | Π | 0 | 0 |

The M/Π example is exchangeable but not radially symmetric, as its two tail
coefficients differ. The public examples check this distinction, the endpoint
identities, CDF calculations, recovery, order and dependence results.

## Extremal median concordance

`Copula.Rank.MedianExtrema` proves that every ordinal sum with split `1/2`
has Blomqvist beta 1. Reflecting its second coordinate gives beta −1 and
Spearman footrule −1/2. With two independent components these constructions
differ from M and W, respectively, giving explicit nonuniqueness examples.
See the [rank equality cases](rank-coefficients.md#equality-cases-and-independence-detection).

For independent components and any interior split, the PQD result combines
with the new strict rank criteria to give positive rho and tau.

## Scope and module map

This API constructs binary bivariate ordinal sums. Repeated application is
available, but a general countable-interval constructor, the converse
decomposition theorem from an interior point with `C(a,a)=a`, and general
ordinal-sum formulas for gamma and xi are not yet formalized. General beta
formulas beyond the midpoint result are also future work.

| Module | Content |
| --- | --- |
| `OrdinalSum.Rescale` | Clipped inverse coordinates, affine embeddings and identities |
| `OrdinalSum.Basic` | Copula validity, constructor, endpoints and regional CDF formulas |
| `OrdinalSum.Measure` | Weighted pushforward law and integration over component squares |
| `OrdinalSum.Blocks` | Block probabilities, almost-sure block agreement and zero cross-block mass |
| `OrdinalSum.Rank` | General rho, tau, footrule and common-split concordance formulas |
| `OrdinalSum.RankExamples` | Benchmark formulas, sharp lower bounds and unique optimal independent-component split |
| `OrdinalSum.Properties` | Recovery, exact ordering, exchangeability, diagonal and extremal results |
| `OrdinalSum.Dependence` | PQD closure and the independent-component example |
| `OrdinalSum.TailDependence` | Tail-ratio identities and equivalence of tail limits |
