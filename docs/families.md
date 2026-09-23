# Copula families and proved coverage

Every constructor in this catalogue returns a `ProbabilityTheory.Copula d`:
a probability measure with proved uniform coordinate marginals. There are no
admissibility axioms, `sorry` proofs, or unverified CDF formulas used as measures.
Import `Copula` for everything, or use the modules below.

## Archimedean families

The convention is the decreasing inverse generator
`C(u) = ψ(∑ᵢ φ(uᵢ))`, with `ψ(φ(u)) = u` on `(0,1]`.
`BivariateGenerator` checks nonnegativity, monotonicity, convexity and inverse
identities. Its `copula` constructor proves all classical copula conditions
before invoking the measure representation theorem. A zero coordinate is
handled separately and gives CDF zero.

`HasArchimedeanGenerator C g` identifies a generator in a specified dimension;
`IsArchimedean C` asserts existence of such a generator. These predicates do
not extend a bivariate admissibility proof to higher dimensions.

| Family | Constructor | Parameters | Dimension | Proved formula or identity |
| --- | --- | --- | --- | --- |
| Independence | `independence d` | None | Any finite `d` | Product CDF; exponential generator in dimension two |
| Clayton | `clayton d θ hθ` | `θ > 0` | Any finite `d` | `(1 + ∑ᵢ(uᵢ^(-θ)-1))^(-1/θ)`; Archimedean identification; parameter limits; bivariate PQD, CI, CDF TP2 and actual MTP2 density; tail pair `(2^(−1/θ),0)` |
| Clayton, negative branch | `claytonNegative θ hθ hn` | `−1 ≤ θ < 0` | 2 | `max(0,u^(−θ)+v^(−θ)−1)^(−1/θ)`; lower bound at −1; NQD, CD and failure of CDF TP2 and of MTP2 density for all negative parameters; tail pair `(0,0)` |
| Gumbel–Hougaard | `gumbel θ hθ` | `θ ≥ 1` | 2 | `exp(-((−log u)^θ+(−log v)^θ)^(1/θ))`; independence at 1; max-stability |
| Joe | `joe θ hθ` | `θ ≥ 1` | 2 | `joe_cdf_full` gives the Table 1 CDF on the closed square; independence at 1; exact tail pair `(0,2−2^(1/θ))` |
| Frank | `frank θ hθ` | `θ > 0` | 2 | `frank_cdf_full` gives the logarithmic CDF on the closed square, including zero axes |
| Frank, negative branch | `frankNegative θ hθ` | `θ < 0` | 2 | `frankNegative_cdf_full` gives the reflected CDF and `frankNegative_cdf_source` proves the printed logarithmic CDF on the closed square |
| BB1 / Clayton–Gumbel | `bb1 θ hθ δ hδ` | `θ > 0`, `δ ≥ 1` | 2 | `bb1_cdf_full` on the closed square; `δ = 1` recovers Clayton |
| BB6 / Joe–Gumbel | `bb6 θ hθ δ hδ` | `θ ≥ 1`, `δ ≥ 1` | 2 | `bb6_cdf_full` on the closed square; `δ = 1` recovers Joe |
| Nelsen 2 | `nelsen2 θ hθ` | `θ ≥ 1` | 2 | `nelsen2_cdf_full` on the closed square; lower bound at 1; exact tail pair `(0,2−2^(1/θ))` |
| Nelsen 7 | `nelsen7 θ` | `θ : I` | 2 | `max(0,θuv+(1−θ)(u+v−1))`; CD; increasing LO; exact xi, rho and tau; CDF TP2 and MTP2 density iff θ=1; W and Π endpoints |
| Nelsen 12 | `nelsen12 θ hθ` | `θ ≥ 1` | 2 | `nelsen12_cdf_full` on the closed square; Clayton at one |
| Nelsen 14 | `nelsen14 θ hθ` | `θ ≥ 1` | 2 | `nelsen14_cdf_full` on the closed square; Clayton at one |
| Genest–Ghoudi / Nelsen 15 | `genestGhoudi θ hθ` | `θ ≥ 1` | 2 | `genestGhoudi_cdf_full` on the closed square; lower bound at 1 |


The shared transformation `g.outerPower θ hθ` sends `ψ(t)` to
`ψ(t^(1/θ))`, for `θ ≥ 1`. Concavity of the power map and convexity of the
decreasing generator prove validity. This supplies Gumbel, BB1, and BB6 without
repeating their measure constructions. `claytonGenerator_copula` proves that
the bivariate generator construction agrees with the existing gamma-frailty
Clayton measure.

The additional transformation `g.innerPower θ hθ` raises ψ to θ and composes
φ with `u ↦ u^(1/θ)`. It preserves convexity for θ≥1 and accommodates finite
zeros. All bivariate Archimedean copulas are proved exchangeable by
`IsArchimedean.isExchangeable`.

Modules: `Copula.Archimedean.Basic`, `Copula.Archimedean.Exponential`,
`Copula.Archimedean.Power`, `Copula.Archimedean.Clayton`,
`Copula.Families.Gumbel`, `Copula.Families.Joe`, `Copula.Families.Frank`, and `Copula.Families.FrankNegative`.

## Extreme-value families

`IsExtremeValue C` is the max-stability identity
`C(u₁^t,…,u_d^t) = C(u)^t` for every `t > 0`, on the entire closed cube.
The identity is proved for every family in this table.

| Family | Constructor | Parameters | Dimension |
| --- | --- | --- | --- |
| Independence | `independence d` | None | Any finite `d` |
| Comonotonic / upper Fréchet bound | `comonotonic d` | None | Any finite `d` |
| Logistic / Gumbel–Hougaard | `gumbel θ hθ` | `θ ≥ 1` | 2 |
| Marshall–Olkin | `marshallOlkin α β` | `α, β : I`, including 0 and 1 | 2 |
| Cuadras–Augé | `cuadrasAuge α` | `α : I` | 2 |
| Asymmetric logistic / Tawn | `tawn θ hθ α β` | `θ ≥ 1`, `α, β : I` | 2 |
| Common-shock extension | `commonShock d a` | `a : Fin d → I` | Any finite `d` |

`cdf_marshallOlkin` gives
`min(u^α,v^β) u^(1-α) v^(1-β)`, including all coordinate and parameter
boundaries. Cuadras–Augé is the equal-weight subfamily. The all-zero and all-one
Marshall–Olkin parameters give independence and comonotonicity respectively. `Rank.MarshallOlkin` proves the full-parameter Spearman rho formula `3αβ/(2α+2β−αβ)`. `Rank.MarshallOlkinConditional` identifies the conditional CDF almost everywhere, and `Rank.MarshallOlkinXi` proves directional Chatterjee xi `2α²β/(3α+β−2αβ)`. Both coefficient formulas include the independence axes and singular positive-weight laws.

The reusable `maxProduct C D a` construction has CDF
`C(uᵢ^aᵢ) D(uᵢ^(1-aᵢ))`. It uses independent samples, transformed power
marginals, and coordinatewise maxima. Zero weights use a constant zero sample.
It preserves extreme-value stability when both inputs have it. Tawn uses
Gumbel and independence as its two inputs. `gumbel_cdf_full` and
`tawn_cdf_full` state the named CDF formulas on the whole closed square,
with explicit grounded values on the zero axes; `tawn_cdf_positive` records
the analytic expression where both logarithms are defined.
The exact reductions `tawn_zero_left`, `tawn_zero_right`, and `tawn_shape_one`
give independence on both weight axes and at shape one; `tawn_one_one`
recovers Gumbel at unit weights. These include zero-coordinate endpoints.
The construction is also useful with inputs that are not extreme-value copulas.

`ExtremeValue.Diagonal` derives the power diagonal `t^κ`, with `1≤κ≤2`,
directly from bivariate max-stability. `TailDependence.ExtremeValue` computes κ
and both tail coefficients for Gumbel, Marshall–Olkin, Cuadras–Augé and Tawn,
including all admitted endpoints. `Rank.PowerDiagonal` gives closed forms
for their Spearman footrule and Blomqvist beta. These results also have generic
versions for arbitrary power-diagonal copulas; see [tail dependence](nelsen.md)
and [rank coefficients](rank-coefficients.md).

Modules: `Copula.Transform.Power`, `Copula.Transform.MaxProduct`,
`Copula.ExtremeValue.Basic`, `Copula.Families.MarshallOlkin`,
`Copula.Families.Gumbel`.

## Elliptical Gaussian scale mixtures

The reusable construction samples `Z ~ N(0,R)` and an independent mixing
variable `T`, and forms `s(T) Z`. The scale is measurable and positive almost
surely. Atomless coordinate marginals and the Sklar factorization are proved.
No density, finite moments, or nonsingularity of `R` is required.

`R` must be positive semidefinite with diagonal one. It is a dispersion
parameter; a covariance matrix of the mixed law need not exist. These are
Gaussian scale mixtures, a subclass of elliptical laws. The package does not
claim a characterization of all elliptical distributions or a radial/characteristic
function characterization of this class.

| Family | Constructor | Mixing law / scale | Extra parameters |
| --- | --- | --- | --- |
| Gaussian | `gaussian R hR hdiag` | Unmixed centered Gaussian | None |
| Student-t | `studentT R hR hdiag ν hν` | `G ~ Gamma(ν/2, rate ν/2)`, `s(G)=1/√G` | Every real `ν > 0` |
| Cauchy | `cauchy R hR hdiag` | Student-t with `ν = 1` | None |
| Symmetric variance-gamma | `varianceGamma R hR hdiag κ hκ` | `G ~ Gamma(κ, rate κ)`, `s(G)=√G` | `κ > 0` |
| Symmetric Laplace | `laplace R hR hdiag` | Variance-gamma with `κ = 1` | None |
| Generalized slash | `slash R hR hdiag q hq` | `E ~ Exp(1)`, `s(E)=exp(E/q)` | `q > 0`; ordinary slash at 1 |
| Normal–lognormal | `normalLognormal R hR hdiag τ` | `T ~ N(0,τ²)`, `s(T)=exp(T)` | `τ : NNReal` |

Every row supports all finite dimensions, including zero. `studentT_one` and
`varianceGamma_one` identify the Cauchy and Laplace special cases. These are
stochastic constructions, with uniform marginal and Sklar theorems; elementary
copula CDFs, densities, tail coefficients, and moment formulas are not asserted.
In particular an identity dispersion matrix need not give an independent
copula when coordinates share a random scale.

Modules: `Copula.Elliptical.ScaleMixture`, `Copula.Families.StudentT`,
`Copula.Families.ScaleMixtures`, and the existing Gaussian modules.

## Polynomial and mixture families

| Family | Constructor | Range / formula | Dimension |
| --- | --- | --- | --- |
| Farlie–Gumbel–Morgenstern | `fgm θ hθ` | `abs θ ≤ 1`; `uv(1+θ(1-u)(1-v))` | 2 |
| Fréchet mixture | `frechet a b ha hb hab` | `a,b ≥ 0`, `a+b ≤ 1`; `aM+bW+(1-a-b)Π` | 2 |
| Mardia | `mardia θ hθ` | `abs θ ≤ 1`; Fréchet weights `θ²(1+θ)/2`, `θ²(1-θ)/2` | 2 |
| Countermonotonic / lower Fréchet bound | `countermonotonic` | `max(0,u+v-1)` | 2 |

FGM's rectangle increment is factored and proved nonnegative for the full
parameter interval. Its actual copula measure has an MTP2 density exactly when
the parameter is nonnegative; the negative exclusion rules out all density
versions, not just the displayed polynomial. Mardia's endpoints `-1,0,1` are respectively the lower
Fréchet bound, independence, and the upper Fréchet bound.

`finiteMixture C w hw hsum` accepts any finite list of copulas and nonnegative
weights summing to one; its CDF is the corresponding weighted sum.
`mix C D a` provides the two-component interface with `a : I`.
These mixture constructors work in every finite dimension. The existing
`reflect` and `reindex` APIs also apply to every new family.

Modules: `Copula.Mixture`, `Copula.Families.FGM`, `Copula.Families.Frechet`.

The additional [ordinal-sum construction](ordinal-sums.md) places two
bivariate copulas on successive intervals. It includes split endpoints,
regional CDF formulas, recovery, exact componentwise ordering, exchangeability
and PQD closure. Its lower and upper tail limits are inherited from the first
and last nonempty blocks. These constructions are not additional named rows
in the Ansari–Rockel family count.
Their probability law and rho, tau, footrule and common-split concordance
formulas are also proved, with sharp fixed-split bounds and a unique optimal
split for independent components.
The converse is constructive: every interior diagonal fixed point yields
two rescaled component copulas, with proved reconstruction and uniqueness
at that split. This includes singular laws and does not require density formulas.

## Vine constructions

`Copula.Vine` combines bivariate families into C-, D-, and regular vines in
every finite dimension. `RVineStructure` supplies variable orders and regular
attachment paths. Pair copulas can be fixed or vary measurably with conditioning
values, including singular laws. Proximity and marginal preservation are proved.
The direct simplified C-vine API additionally has its explicit CDF recursion
and all-independence identity. See the [vine guide](vines.md) for the constructors,
conventions, and exact proved coverage.

## Additional checked family properties

Fréchet and Mardia have exact CI/CD and Lebesgue-density classifications,
including singular endpoints. Both have a TP2 Lebesgue density exactly at
independence. See [positive dependence](positive-dependence.md).

Nelsen 7 has xi=1-theta and exact logarithmic rho and tau for all theta in [0,1], a checked conditional CDF,
and exact Schur comparison in both directions, with parameter order reversed.
Its only CI member is independence; every member is CD.

{{ lean:nelsen7-xi }}
{{ lean:nelsen7-rho }}
{{ lean:nelsen7-tau }}
{{ lean:nelsen7-schur }}

## Scope and next extensions

This catalogue contains 27 named families/special cases; overlapping classes
are not counted twice. It distinguishes proved analytic CDFs from stochastic
constructions. General multivariate Archimedean admissibility, Ali–Mikhail–Haq, BB7/BB8, Galambos, Hüsler–Reiss, Plackett,
Pickands representations, and further family-specific dependence formulas remain future work.
The [rank API](rank-coefficients.md) includes closed forms for all six
coefficients of FGM, Fréchet and Mardia, on their full parameter domains.
The Fréchet and Mardia tau formulas are `(a−b)(a+b+2)/3` and `θ³(θ²+2)/3`;
their xi formulas are `(a−b)²+ab` and `θ⁴(1+3θ²)/4`, with all singular
boundaries included. The rank documentation lists the complete formulas.
The [ordering API](orders.md) proves exact FGM
parameter ordering, FGM Schur order by absolute parameter, and comparison
results for mixtures and extremal copulas.
The [tail-dependence API](nelsen.md) gives both tail limits for FGM, Fréchet,
Mardia, Gumbel, Marshall–Olkin, Cuadras–Augé and Tawn, together with the
independence and Fréchet-bound benchmarks. Tail formulas for the other
analytic and elliptical families remain future work.
The bivariate validity theorem does not establish the new Archimedean families
in higher dimensions, even for ranges known to be valid mathematically.

The complete [Ansari–Rockel index](ansari-rockel.md) tracks all 38 paper
families, including those not yet implemented. Its property and formula tables
are reference targets, not additional proved constructors or theorems.

## Mathematical references

- [The R copula authors' family documentation](https://stat.ethz.ch/CRAN/web/packages/copula/refman/copula.html): standard family names, parameter conventions, mixtures and transformations.
- [VineCopula's BB1 constructor](https://tnagler.github.io/VineCopula/reference/BB1Copula.html) and [vinecopulib's family catalogue](https://vinecopulib.github.io/vinecopulib/namespacevinecopulib.html): two-parameter Archimedean naming and ranges.
- [Gudendorf and Segers, *Extreme-Value Copulas*](https://arxiv.org/abs/0911.1015): max-stability and extreme-value families.
- [Demarta and McNeil, *The t Copula and Related Copulas*](https://doi.org/10.1111/j.1751-5823.2005.tb00254.x): the Gaussian-mixture construction of Student-t copulas.

The formal statements and their checked proofs in this repository specify
the exact implemented coverage; the references also discuss results beyond it.
