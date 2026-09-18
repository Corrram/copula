# Orders on copulas

```lean
import Copula.Order
```

Declarations live in `ProbabilityTheory.Copula`, except the generic lattice
predicate `ProbabilityTheory.IsSupermodular`. Orders have explicit names;
there is no global `LE (Copula d)` instance.

## Conventions

| Predicate | Dimension | Meaning of `C` below `D` |
| --- | --- | --- |
| `LowerOrthantLE` | Any finite dimension | `C.cdf u ≤ D.cdf u` at every threshold |
| `UpperOrthantLE` | Any finite dimension | `C.survival u ≤ D.survival u` at every threshold |
| `ConcordanceLE` | Any finite dimension | Both orthant comparisons |
| `SupermodularLE` | Any finite dimension | Smaller expectations of every bounded measurable supermodular function |
| `SchurLE` | Two | Smaller convex functionals of the conditional CDF of coordinate 1 given coordinate 0, at every threshold |

Lower orthant order follows the copula convention of increasing CDFs. Some
stochastic-order literature uses the opposite convention for random vectors;
the formula above fixes the orientation unambiguously.

`survival C u` is the probability of the closed upper orthant `Set.Ici u`.
`survival_eq_strict` proves equality with the event `∀ i, u i < x i`:
uniform marginals give every coordinate face measure zero, including for
singular copulas. This strict event is not `Set.Ioi u` in the pointwise partial
order. All-dimension statements include dimension zero.

Supermodularity means

```text
f(x) + f(y) ≤ f(x ⊓ y) + f(x ⊔ y).
```

The definition uses bounded measurable tests. No equivalence with unrestricted
integrable tests or smooth mixed-derivative tests is claimed here.

For Schur order, put `K_C(u,t) = P(V ≤ t | U = u)`. The definition is the
continuous convex-test formulation of majorization:

```text
∫ φ(K_C(u,t)) du ≤ ∫ φ(K_D(u,t)) du
```

for every `t ∈ [0,1]` and every continuous real function convex on `[0,1]`.
Both conditional functions have mean `t`. Tests are globally continuous but
need only be convex on the unit interval. Conditional kernels are defined for
all copulas, so this formulation also covers deterministic dependence.
`schurLE_iff_of_kernel_ae` permits replacement by any almost-everywhere equal
kernel version. The equivalence to a decreasing-rearrangement definition has
not been formalized in this repository.

## Proved comparisons

* Reflexivity, transitivity and antisymmetry for lower orthant, upper orthant,
  concordance and supermodular order.
* Full coordinate reflection interchanges the orthant orders and preserves
  concordance order.
* In two dimensions,
  `survival C u = 1 - u₀ - u₁ + C.cdf u`; consequently lower orthant, upper
  orthant and concordance orders coincide.
* Supermodular order implies concordance order in every finite dimension.
* In two dimensions the countermonotonic copula is least and the comonotonic
  copula greatest for concordance order.
* Lower orthant order is preserved by mixtures with a common weight.
  Increasing the weight of the larger component increases the mixture.
* Binary ordinal sums preserve lower orthant order componentwise. At a fixed
  interior split, comparison of the sums is equivalent to comparison of both
  components; see the [ordinal-sum API](ordinal-sums.md).
* PQD is equivalent to being above independence in lower orthant order.
* FGM copulas are ordered exactly by their parameter on the full `[-1,1]`
  interval: `C_θ ≤lo C_η ↔ θ ≤ η`.

`integral_cdf_swap` proves the cross-concordance identity

```text
∫ C dD = ∫ D dC.
```

It supplies the proof that Kendall's tau is increasing in lower orthant order.
The order API also exposes monotonicity of Spearman's rho, Spearman's footrule,
Gini's gamma and Blomqvist's beta.

`Order.StrictSpearman` strengthens rho monotonicity: if `C ≤lo D`, then
`rho(C) = rho(D)` holds exactly when `C = D`. Consequently `C ≠ D` gives
`rho(C) < rho(D)`. The same statements hold for concordance order in dimension
two. The proof uses continuity of the CDFs and full support of uniform volume;
it also covers singular copulas. Strict monotonicity of the other coefficients
is not asserted.

Within PQD or NQD, zero rho and zero tau each characterize independence.
Dependent PQD copulas therefore have positive rho and tau; dependent
NQD copulas have negative rho and tau.

## Schur order and predictability

`SchurLE` is a preorder on copulas. The implementation proves:

* Independence is below every copula, and `C ≤Schur Π` holds exactly when
  `C = Π`.
* Every copula lies below any copula whose second coordinate is almost surely
  a measurable function of its first coordinate.
* In particular, both `M` and `W` are greatest elements and are Schur-equivalent.
* A measure-preserving reparametrization of the conditioning variable, whenever
  it relates the conditional CDFs almost everywhere at each threshold, preserves
  both Schur comparisons.
* Chatterjee's directional xi is increasing in Schur order.
* Mixtures preserve a common Schur upper bound: if both `C` and `D` are below
  `E`, then so is every convex mixture of `C` and `D`.
* Adding independence reduces predictability: `a C + (1−a) Π ≤Schur C`.
  These diluted copulas are increasing in Schur order as `a` increases.
* Schur order is not antisymmetric on copulas.

There is no general implication in either direction between concordance and
Schur comparison. Formal examples show why: `W ≤lo Π`, but `W` is not below
`Π` in Schur order; `M ≤Schur W`, but `M` is not below `W` in lower orthant order.

## Module map

| Module | Main content |
| --- | --- |
| `Order.Survival` | Upper orthants, boundary nullity and reflection/CDF formulas |
| `Order.Orthant` | Three orthant/concordance predicates and order laws |
| `Order.Rank` | Cross-concordance symmetry, rank monotonicity and extrema |
| `Order.StrictSpearman` | Strict rho monotonicity and rho/tau independence criteria within PQD/NQD |
| `Order.FGM` | Exact FGM parameter comparisons |
| `Order.Frechet` | Monotonicity in the upper-bound weight and antitonicity in the lower-bound weight |
| `Order.SymmetricSchur` | Two-direction `SchurBothLE`, transposition and reduction for exchangeable/Archimedean copulas |
| `Order.FGMSchur` | Exact directional and two-direction FGM Schur order: `abs theta ≤ abs eta` |
| `Order.Schur` | Convex-test preorder, kernel versions, rearrangement invariance and xi |
| `Order.SchurExamples` | Unique least element and counterexamples to conflating orders |
| `Order.SchurMixture` | Convex upper-bound sets, attenuation by independence, and monotonicity in retained weight |
| `Order.Supermodular` | Bounded measurable test order and orthant implications |

## Further results to formalize

The current results do not yet include the converse from bivariate concordance
to supermodular order, the decreasing-rearrangement characterization of Schur
order, or equivalence of Schur and lower orthant orders within the SI class.
That last result needs further work connecting the package's chord-concavity
definition of SI to monotone versions of conditional distributions.

Generator criteria for Archimedean ordering, Pickands-function comparisons for
extreme-value copulas, and correlation-parameter comparisons for Gaussian and
elliptical copulas are also future extensions. Their family constructors are
already available; these comparison theorems are not asserted by this module.

## References

* Ansari and Rockel, [Dependence properties of bivariate copula families](https://arxiv.org/abs/2310.17307),
  for directional Schur comparison and its distinction from lower orthant order.
* Ansari and Rüschendorf, [Upper risk bounds in internal factor models with constrained specification sets](https://link.springer.com/article/10.1186/s41546-020-00045-y),
  for orthant and supermodular comparison conventions.
