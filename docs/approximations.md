# Grid constructions, shuffles and Bernstein copulas

Import `Copula.Checkerboard`, `Copula.Shuffle`, `Copula.Bernstein`, or the
umbrella `Copula`. All constructors below return actual measure-based
`Copula 2` values. Their uniform marginals and nonnegative rectangle
increments are proved, with no extra copula-validity assumption on callers.

## Coverage

| Construction | Formalized scope and guarantees |
| --- | --- |
| Ordinal sums | Existing binary API, arbitrary finite partitions, and countably many adjacent blocks exhausting `[0,1]`; see [ordinal sums](ordinal-sums.md) |
| Ordinal sums of Π | `ordinalSumPi` and `countableOrdinalSumPi`, with explicit CDF formulas |
| Shuffles of min | Arbitrary finite positive strip widths, a length-matching permutation, and an independent reflection choice for each segment |
| Checkerboard | Rectangular, nonuniform grids; arbitrary nonnegative cell probabilities with the specified row and column sums |
| Check-min | Same grids and matrices, using comonotonic local coordinates |
| Bernstein | Arbitrary positive degrees in each coordinate, the tensor polynomial formula, copula validity, independence preservation and uniform convergence |

These are bivariate constructions. Closed-form rank-coefficient formulas
for these new families, shuffle density, and higher-dimensional grid and
Bernstein constructors are not asserted here. The binary ordinal-sum rank
results remain available in their existing modules.

## Partitions and cell probabilities

`IntervalPartition n` contains `n+1` strictly increasing knots, beginning
at zero and ending at one. Its `width i` is positive. Its clipped local
coordinate is

```text
coord_i(u) = clamp((u - point_i) / width_i, 0, 1).
```

`IntervalPartition.uniform n hn` constructs equal-width cells from
`hn : 0 < n`. The endpoint requirements rule out an empty partition;
zero-width cells are excluded rather than silently divided by zero.

`CellMass P Q` stores an `m × n` matrix of **probabilities**, with
nonnegative entries, row sums `P.width i` and column sums `Q.width j`.
On a uniform grid these sums are `1/m` and `1/n`, respectively. Zero
entries are allowed. `CellMass.product P Q` is the product of the width
vectors. Its checkerboard is exactly independence.

`C.cellMass P Q` constructs the matrix directly from the rectangle
increments of any copula `C`. Matrix admissibility, including both
marginal identities, is proved by two-increasingness and telescoping.

## Local copulas and exact interpolation

Given `A : CellMass P Q` and local copulas `D i j`, `A.patchwork D` has CDF

```text
sum_i sum_j A.mass i j * D_ij(coord_i(u), coord_j(v)).
```

The specializations are:

- `A.checkerboard`: each `D_ij = Π`, so the local factor is a product.
- `A.checkMin`: each `D_ij = M`, so the local factor is a minimum.
- `A.checkW`: each `D_ij = W`, so the local factor is `max(s+t-1,0)`.

The same formulas cover cell boundaries and the outer boundary.
`CellMass.cellMass_patchwork` proves that sampling the result recovers
exactly `A.mass i j`, independently of the local copulas.
`CellMass.checkerboard_le_checkMin` gives their pointwise comparison.

For a source copula, `C.checkerboard P Q` and `C.checkMin P Q` first
sample its cell probabilities. `cdf_cellMass_patchwork_point` proves
that every local filling agrees with `C` at every grid vertex.
The convenient specializations are `cdf_checkerboard_point` and
`cdf_checkMin_point`.

{{ lean:grid-interpolation }}

`abs_cdf_cellMass_patchwork_sub_le_mesh` bounds the CDF error everywhere
by `dx + dy` when the row and column widths are at most `dx` and `dy`.
In particular, `abs_cdf_checkerboard_uniform_sub_le` and
`abs_cdf_checkMin_uniform_sub_le` bound the error by `1/m + 1/n`.
The bound holds for singular source copulas as well.
`tendstoUniformly_checkerboard` and `tendstoUniformly_checkMin` prove
uniform convergence along refining uniform grids, as a consequence of the
general `tendstoUniformly_cellMass_patchwork` theorem.

{{ lean:grid-error }}

## Shuffles of min

`shuffleOfMin P Q perm hwidth flipped` uses one segment in each strip
pair `(i, perm i)`. `hwidth` states that matched strips have the same
length; each segment has that length as probability mass. `flipped i`
selects decreasing (`true`) or increasing (`false`) orientation.

`cdf_shuffleOfMin` gives the weighted sum of the corresponding local
`W` or `M` CDFs. `uniformShuffleOfMin n hn perm` is the convenient
straight equal-width case. `shuffleOfMin_refl` identifies the straight
identity shuffle with `M`.

## Bernstein copulas

For positive `m,n`, `C.bernstein m n hm hn` has the CDF

```text
sum_{i=0}^m sum_{j=0}^n C(i/m,j/n) B_{i,m}(u) B_{j,n}(v),
B_{i,m}(u) = choose(m,i) u^i (1-u)^(m-i).
```

`bernsteinCDF_eq_sum` connects the constructor to mathlib's Bernstein
basis. The proof of `isClassical_bernsteinCDF` uses the derivative
identity for Bernstein combinations to establish monotonicity from
ordered coefficients, then applies it to copula rectangle increments.
Degree zero is deliberately excluded from the copula constructor.

{{ lean:bernstein-valid }}

`bernstein_independence` proves that smoothing Π returns Π.
`bernstein_one_one` proves that degree `(1,1)` returns Π for every source.
The public examples also check the nontrivial value `B_{2,2}(M)(1/2,1/2)=5/16`.

`abs_bernsteinCDF_sub_le` bounds the error at `(u,v)` by
`sqrt(u(1-u)/m) + sqrt(v(1-v)/n)`. Its uniform specialization bounds it by
`sqrt(1/(4m)) + sqrt(1/(4n))`. Finally, `tendstoUniformly_bernstein` proves
uniform convergence along degrees `(k+1,k+1)`.

{{ lean:bernstein-convergence }}

## Modules

| Module | Content |
| --- | --- |
| `Patchwork.Basic` | General finite validity and monotonicity under local CDF order |
| `Patchwork.Partition` | Nonuniform partitions, clipping and telescoping |
| `Patchwork.Grid` | Cell matrices, sampling, local fillings and named families |
| `Patchwork.Approximation` | Grid interpolation, cell recovery and uniform error bounds |
| `OrdinalSum.Finite` | Finite sums, Π specialization and binary compatibility |
| `OrdinalSum.Countable` | Increasing countable partitions, summability and CDF series |
| `Shuffle` | Unequal-width signed shuffles and straight uniform shuffles |
| `Bernstein.Basis` | Bernstein derivative and shape-preservation lemmas |
| `Bernstein.Basic` | Tensor formula, validity and benchmark identities |
| `Bernstein.Approximation` | Error bounds and uniform convergence |

For the conventional family definitions and terminology, see
[Rockel, Measures of association for approximating copulas, §2](https://arxiv.org/html/2505.08045v2#S2)
and [Cottin–Pfeifer, From Bernstein polynomials to Bernstein copulas](https://uol.de/f/5/inst/mathe/personen/dietmar.pfeifer/Publ/P107.pdf).
