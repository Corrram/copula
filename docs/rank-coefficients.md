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
a singular copula. Equivalence to a partial-derivative formula, the converse
functional-dependence characterization, and the zero-if-and-only-if-independence
characterization are not yet formalized.

## Algebra and family formulas

`spearmanRho_eq_one_sub` and `spearmanRho_eq_neg_one_add` give the two square-distance
identities `rho = 1 − 6 E[(U−V)²] = −1 + 6 E[(U+V−1)²]`.
`spearmanRho_eq_integral_cdf` connects the moment and CDF definitions via Fubini.

Rho, footrule, gamma and beta are proved monotone under pointwise CDF ordering.
Their `*_mix` theorems prove affine behavior under `Copula.mix C D a`, where
`a` is the weight on `C`. No affine identity is asserted for tau or xi.

For FGM with any parameter `theta ∈ [-1,1]`, `Copula.Rank.FGM` proves:

| Coefficient | Value | Theorem |
| --- | --- | --- |
| rho | `theta / 3` | `spearmanRho_fgm` |
| footrule | `theta / 5` | `spearmanFootrule_fgm` |
| gamma | `4 theta / 15` | `giniGamma_fgm` |
| beta | `theta / 4` | `blomqvistBeta_fgm` |

Further family-specific formulas, permutation/reflection identities, Kendall's
probabilistic concordance interpretation, and sample estimators remain future
work. The current integration and conditional-kernel APIs provide the basis
for those additions.

## Module map

- `Rank.Integration`: uniform moments, coordinate integrals, and benchmark measure integrals.
- `Rank.Basic`: the five classical definitions, basic bounds and CDF ordering.
- `Rank.Spearman`, `Rank.SpearmanCDF`: distance formulas, rho bounds and CDF formula.
- `Rank.Benchmarks`: classical benchmark values and footrule/gamma bounds.
- `Rank.Conditional`: conditional kernel, conditional CDF and marginal identities.
- `Rank.Chatterjee`, `Rank.ChatterjeeExamples`: xi, bounds, version invariance and examples.
- `Rank.Mixture`, `Rank.FGM`: affine identities and exact FGM formulas.
