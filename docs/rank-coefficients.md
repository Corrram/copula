# Population rank dependence coefficients

Import `Copula.Rank` (or `Copula`) for the six bivariate coefficients. These
are population functionals of a copula, not finite-sample rank statistics or
numerical integration routines. Every definition applies to any `Copula 2`,
including singular copulas.

Write `C(u,v)` for the CDF, `dC` for the copula probability measure, and
`K(u,[0,t])` for the conditional probability of the second coordinate being at
most `t`, given that the first is `u`. Unspecified integrals below are with
respect to uniform volume on the unit interval or square.

| Lean accessor | Definition | Proved range |
| --- | --- | --- |
| `C.spearmanRho` | `12 ∫ uv dC(u,v) − 3`, also `12 ∫ C(u,v) du dv − 3` | `[-1,1]` |
| `C.kendallTau` | `4 ∫ C(u,v) dC(u,v) − 1` | `[-1,1]` |
| `C.spearmanFootrule` | `6 ∫ C(t,t) dt − 2` | `[-1/2,1]` |
| `C.giniGamma` | `4 ∫ [C(t,t) + C(t,1−t)] dt − 2` | `[-1,1]` |
| `C.blomqvistBeta` | `4 C(1/2,1/2) − 1` | `[-1,1]` |
| `C.chatterjeeXi` | `6 ∫∫ K(u,[0,t])² du dt − 2` | `[0,1]` |

The footrule normalization is the population copula convention in
[Kokol Bukovšek and colleagues' treatment of footrule, gamma and beta](https://arxiv.org/abs/2009.06221).
It is distinct from the unnormalized sum of absolute differences of sample
ranks. In particular, its countermonotonic value is `−1/2`.

## Conditional CDFs and classical derivatives

`Rank.ConditionalDerivative` proves that the conditional CDF equals the first
partial derivative of the copula CDF almost everywhere in the conditioning
coordinate, for every fixed threshold. `cdfSection C v` extends the section
constantly outside the unit interval; its derivative agrees with the ordinary
partial derivative in the interior, and endpoints have zero measure.
`chatterjeeXi_eq_integral_deriv` therefore identifies the conditional-distribution
definition of xi with the classical double integral of the squared derivative.
The proof uses disintegration and the almost-everywhere fundamental theorem
of calculus. It applies to singular copulas and requires no density assumption.

`Rank.ChatterjeeCrossMixture` proves `chatterjeeCross_mix_right`, the affine
mixture identity for the polarized xi functional. Together with the existing
squared-distance and comonotonic cross-term identities, this supports sharp
coefficient bounds by comparison with mixtures of independence and M.

## Checked benchmark values

All entries in this table are proved and registered as simplification lemmas.
They also establish that the stated range bounds are sharp.

| Copula | rho | tau | footrule | gamma | beta | xi |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Independence `Π` | 0 | 0 | 0 | 0 | 0 | 0 |
| Comonotonicity `M` | 1 | 1 | 1 | 1 | 1 | 1 |
| Countermonotonicity `W` | −1 | −1 | −1/2 | −1 | −1 | 1 |

For example:

```lean
import Copula.Rank

open ProbabilityTheory

example (C : Copula 2) : C.chatterjeeXi ∈ Set.Icc 0 1 :=
  C.chatterjeeXi_mem_Icc

example : Copula.countermonotonic.chatterjeeXi = 1 := by simp
```

## Equality cases and independence detection

`Rank.Extrema` and `Rank.MedianExtrema` prove the equality cases:

| Equality | Equivalent condition |
| --- | --- |
| `rho = 1`, `tau = 1`, `gamma = 1`, or `footrule = 1` | `C = M` |
| `rho = −1`, `tau = −1`, or `gamma = −1` | `C = W` |
| `beta = 1` | `C(1/2,1/2) = 1/2` |
| `beta = −1` | `C(1/2,1/2) = 0` |
| `footrule = −1/2` | `beta = −1`, also `δ(t) = max(0,2t−1)` for every t |

The corresponding strict-bound lemmas are available, for example
`spearmanRho_lt_one_iff` and `neg_one_lt_kendallTau_iff`.
`Copula.Support` identifies M with almost-sure equality of the uniform
coordinates and W with their sum being one almost surely. No density
assumptions occur in these characterizations.

The beta conditions do not determine the whole copula. Every ordinal sum
with split `1/2` has beta 1; reflecting its second coordinate gives beta −1
and footrule −1/2. Choosing independent copulas as both components gives
explicit witnesses different from M and W. Thus minimal footrule, unlike
maximal footrule, does not determine a unique copula.

`OrdinalSum.CutConsequences` supplies the converses: beta 1 characterizes
ordinal sums with split `1/2`, with a unique component pair at that split;
beta −1 characterizes their second-coordinate reflections. It follows that
beta 1 forces `rho≥1/2`, `tau≥0`, and `footrule≥1/4`, whereas beta −1 forces
`rho≤−1/2` and `tau≤0`. The equal-split W/W copula and its reflection attain
these bounds. See the [decomposition API](ordinal-sums.md#converse-decomposition-and-unique-components).

`Order.StrictSpearman` proves that distinct copulas comparable in lower
orthant or concordance order have strictly different rho. Within either the
PQD or NQD class, rho vanishes exactly at independence. The same equivalence
holds for tau, using `rho ≤ 3 tau` for PQD and `3 tau ≤ rho` for NQD. These
are conditional independence criteria: zero rho or tau alone is insufficient,
as the equal M/W mixture already demonstrates.

## Concordance probabilities and Kendall's tau

`C.concordanceQ D = 4 ∫ C dD − 1` is the bivariate concordance function Q.
It is symmetric, belongs to `[-1,1]`, increases under lower orthant order in
either argument, and equals Kendall's tau when both arguments are `C`.

For independent observations `X ~ C` and `Y ~ D`, `concordantPairs` is the
event `(X₀−Y₀)(X₁−Y₁)>0`; `discordantPairs` uses `<0`. In Lean their joint law
is `C.toMeasure.prod D.toMeasure`. `Rank.ConcordanceProbability` proves

```text
P(concordance) = (1+Q(C,D))/2
P(discordance) = (1−Q(C,D))/2
Q(C,D) = P(concordance) − P(discordance).
```

The probabilities sum to one. Uniform marginals imply that each coordinate
has probability zero of a tie across these independent observations; no
density is needed. Taking `D=C` gives Kendall's interpretation. Tau is `1`
exactly when almost every pair is concordant, `−1` exactly when almost every
pair is discordant, and zero exactly when those probabilities are equal.
Zero tau does not in general imply independence.

Pairing Q with the benchmarks links the classical coefficients:

```text
Q(C,Π) = rho(C)/3
Q(C,M) = (2 footrule(C)+1)/3
Q(C,W) = gamma(C) − (2 footrule(C)+1)/3.
```

In particular `gamma(C)=Q(C,M)+Q(C,W)` and `Q(M,W)=0`.

## Chatterjee's direction and conditional distributions

`C.chatterjeeXi` measures dependence of **coordinate 1 given coordinate 0**.
To ask about the opposite direction, first swap the coordinates using
`C.reindex ![1,0]`. The API does not symmetrize xi.

`C.conditionalKernel` uses mathlib's regular conditional distribution;
`C.conditionalCDF u t` is its real-valued mass on `Set.Iic t`. The library proves
joint measurability, integrability, bounds between zero and one, and the identity
`∫ K(u,[0,t]) du = t`. It also proves

```text
xi(C) = 6 ∫∫ (K(u,[0,t]) − t)² du dt.
```

`chatterjeeXi_eq_of_kernel_ae` permits replacement by any almost-everywhere
equal kernel version. `chatterjeeXi_eq_one_of_function` proves xi equals one
when the second coordinate is almost surely a measurable function of the first.
This includes both increasing and decreasing deterministic dependence.

The conditional-distribution definition follows the population coefficient
introduced in [Chatterjee, A new coefficient of correlation](https://arxiv.org/abs/1909.10140).
Using a kernel avoids assuming a density or choosing pointwise derivatives of
a singular copula. `chatterjeeXi_eq_zero_iff` now proves that xi is zero exactly
at independence, and `chatterjeeXi_pos_iff` gives strict positivity for every
other copula. Equivalence to a partial-derivative formula and the converse
functional-dependence characterization at xi=1 are not yet formalized.

The proof uses `conditionalCDFDistanceSq C D = ∫∫ (K_C−K_D)²`. This quantity
is symmetric, nonnegative, and zero exactly when `C=D`; xi equals six times
the squared distance to independence. `ext_conditionalCDF_ae` identifies
copulas from nested almost-everywhere equality of their conditional CDFs.
Continuity of the copula CDF handles exceptional threshold sets without
assuming a jointly continuous conditional kernel.

## Algebra and family formulas

`spearmanRho_eq_one_sub` and `spearmanRho_eq_neg_one_add` give the two square-distance
identities `rho = 1 − 6 E[(U−V)²] = −1 + 6 E[(U+V−1)²]`.
`spearmanRho_eq_integral_cdf` connects the moment and CDF definitions via Fubini.

Rho, footrule, gamma and beta are proved monotone under pointwise CDF ordering.
`Copula.Order.Rank` adds Kendall's tau using symmetry of the cross-concordance
integral. `Copula.Order.Schur` proves monotonicity of xi in directional Schur
order. See [comparison orders](orders.md) for the precise conventions.
The `*_mix` theorems for rho, footrule, gamma and beta prove affine behavior under `Copula.mix C D a`, where
`a` is the weight on `C`. Tau and xi have quadratic mixture identities.

`Rank.KendallMixture` proves

```text
tau(a C + (1−a) D)
  = a² tau(C) + (1−a)² tau(D) + 2a(1−a) Q(C,D)
tau(∑ᵢ wᵢ Cᵢ) = ∑ᵢ ∑ⱼ wᵢ wⱼ Q(Cᵢ,Cⱼ).
```

The finite weights are nonnegative and sum to one. Q is affine in each
argument separately. Mixing with independence gives
`tau(a C+(1−a)Π)=a² tau(C)+(2/3)a(1−a)rho(C)`; mixing with M or W gives
formulas involving footrule and gamma. In particular the equal mixture of
M and Π has tau `5/12`, and `kendallTau_not_affine` formally rules out a
general affine identity. The M/W segment has tau `2a−1`.

`conditionalCDF_finiteMixture` and `conditionalCDF_mix` give almost-everywhere
conditional CDF identities for finite and binary mixtures. The weights remain
constant because the conditioning marginals are uniform.

`Rank.ChatterjeeMixture` proves the exact quadratic identity

```text
xi(a C + (1−a) D)
  = a xi(C) + (1−a) xi(D) − 6a(1−a) conditionalCDFDistanceSq(C,D).
```

Consequently xi is convex, and the inequality is strict when `C≠D` and
`0<a<1`. Equality for an interior weight characterizes `C=D`. Mixing with
independence gives `xi(a C + (1−a) Π) = a² xi(C)`, including both endpoints.
The equivalent polarized formula uses `chatterjeeCross C D = 6∫∫ K_C K_D−2`.
This cross functional is symmetric, equals xi on the diagonal, vanishes when
one input is Π, and can be negative. Pairing with M gives Spearman's footrule,
which supplies an explicit formula for mixing an arbitrary copula with M.

For FGM with any parameter `theta ∈ [-1,1]`, `Copula.Rank.FGM` proves:

| Coefficient | Value | Theorem |
| --- | --- | --- |
| rho | `theta / 3` | `spearmanRho_fgm` |
| footrule | `theta / 5` | `spearmanFootrule_fgm` |
| gamma | `4 theta / 15` | `giniGamma_fgm` |
| beta | `theta / 4` | `blomqvistBeta_fgm` |
| tau | `2 theta / 9` | `kendallTau_fgm` in `Rank.FGMKendall` |
| xi | `theta² / 15` | `chatterjeeXi_fgm` in `Rank.FGMChatterjee` |

Thus all six library coefficients now have proved FGM formulas.
`conditionalCDF_fgm` identifies the continuous conditional CDF version
`v + theta (1−2u) v(1−v)` almost everywhere in u for each v.
The reusable `conditionalCDF_ae_eq_of_integral` identifies such versions from
their lower-interval integrals without assuming a pointwise derivative theorem.

`Rank.Frechet`, `Rank.FrechetKendall`, and `Rank.FrechetChatterjee` prove all
six Fréchet and Mardia formulas, including singular boundaries:

| Coefficient | Fréchet, `a,b≥0`, `a+b≤1` | Mardia, `abs theta≤1` |
| --- | --- | --- |
| rho | `a−b` | `theta³` |
| tau | `(a−b)(a+b+2)/3` | `theta³(theta²+2)/3` |
| footrule | `a−b/2` | `theta²(1+3theta)/4` |
| gamma | `a−b` | `theta³` |
| beta | `a−b` | `theta³` |
| xi | `(a−b)²+ab` | `theta⁴(1+3theta²)/4` |

Zero xi is equivalent to `a=b=0` or `theta=0`, respectively. Zero tau is
equivalent to `a=b` or `theta=0`. The equal mixture of M and W has tau zero
but xi `1/4`, giving a checked dependent copula with zero tau.
The full [Ansari–Rockel expression index](ansari-rockel.md)
records the remaining formula targets and flags source discrepancies; these
reference expressions are not yet all formalized.

`Rank.PowerDiagonal` proves, for any copula with diagonal `t^κ`,
`footrule = 6/(κ+1)−2` and `beta = 2^(2−κ)−1`. Every bivariate extreme-value
copula has such a diagonal, with κ its extremal coefficient in `[1,2]`.
The family theorems specialize these expressions using:

| Family | κ |
| --- | --- |
| Gumbel–Hougaard | `2^(1/θ)` |
| Marshall–Olkin | `2−min(α,β)` |
| Cuadras–Augé | `2−α` |
| Tawn | `2−α−β+(α^θ+β^θ)^(1/θ)` |

All admissible parameter endpoints are included. These two coefficients
depend only on the diagonal; no analogous claim is made for rho, tau or xi.

`Rank.Symmetry` proves transposition and survival-copula invariance for all five
classical coefficients. Reflecting either coordinate negates rho, tau, gamma
and beta. No such sign rule is asserted for footrule; see [the symmetry table](nelsen.md).

Further family-specific formulas, transformation identities for xi, and
sample estimators remain future work. The current integration and
conditional-kernel APIs provide the basis for those additions.

Binary ordinal sums have exact formulas for rho, tau, footrule and concordance
between two sums with the same split. Deficits from one scale cubically for
rho and quadratically for tau and footrule. See the
[ordinal-sum rank formulas and sharp bounds](ordinal-sums.md#rank-coefficients-and-sharp-bounds),
including independent and countermonotonic components and their endpoint cases.

## Nelsen 7 and Frechet optimization

Nelsen 7 has xi=1-theta on the full closed interval, including W at zero
and independence at one. Its step conditional CDF is identified by recovering
the actual copula CDF from lower-interval integrals; no density is assumed.

{{ lean:nelsen7-xi }}

Over the full Frechet weight simplex, xi plus footrule is at least -1/16,
with equality exactly at a=0, b=1/4. Thus the unique minimizer is
three quarters independence plus one quarter W. This is a family-restricted
optimization result, not a bound for arbitrary copulas.

{{ lean:frechet-objective-minimum }}
{{ lean:frechet-objective-equality }}

## Module map

- `Rank.Integration`: uniform moments, coordinate integrals, and benchmark measure integrals.
- `Rank.Basic`: the five classical definitions, basic bounds and CDF ordering.
- `Rank.Spearman`, `Rank.SpearmanCDF`: distance formulas, rho bounds and CDF formula.
- `Rank.Benchmarks`: classical benchmark values and footrule/gamma bounds.
- `Rank.Extrema`: equality cases and strict bounds for rho, tau, footrule and gamma.
- `Rank.MedianExtrema`: beta equality cases, minimal diagonals and footrule, and nonuniqueness witnesses.
- `Copula.Support`: almost-sure characterizations of M and W.
- `Order.StrictSpearman`: strict rho comparison and independence criteria within PQD/NQD.
- `Rank.Conditional`: conditional kernel, conditional CDF and marginal identities.
- `Rank.Chatterjee`, `Rank.ChatterjeeExamples`: xi, bounds, version invariance and examples.
- `Rank.Mixture`, `Rank.FGM`: affine identities and exact FGM formulas.
- `Rank.Symmetry`: transpose, reflection and survival-copula identities.
- `Rank.PowerDiagonal`: footrule and beta for power diagonals and four extreme-value families.
- `Rank.ConditionalMixture`: finite and binary mixture conditional CDFs.
- `Rank.ConditionalDistance`: squared distance, separation, and xi=0 iff independence.
- `Rank.ChatterjeeCross`, `Rank.ChatterjeeMixture`: polarization, exact mixture identities and strict convexity.
- `Rank.FrechetChatterjee`: Fréchet and Mardia xi formulas, including endpoints.
- `Rank.Concordance`: Q, symmetry, range, ordering, affine identities, and links to rho/footrule/gamma.
- `Rank.ConcordanceProbability`: independent-pair probabilities, null ties, and the probabilistic tau interpretation.
- `Rank.KendallMixture`: finite and binary mixture formulas and non-affinity.
- `Rank.FrechetKendall`: Fréchet and Mardia tau, footrule, gamma, beta and zero-tau parameters.
- `OrdinalSum.Rank`, `OrdinalSum.RankExamples`: ordinal-sum formulas, sharp fixed-split bounds and optimization for independent components.

- `Rank.Nelsen7`: conditional CDF and exact xi on the full parameter interval.
- `Rank.FrechetOptimization`: exact xi-plus-footrule minimum and unique parameters.
