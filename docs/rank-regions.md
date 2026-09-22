# Pairwise rank regions

Import `Copula.Rank.Region`, `Copula.Rank`, or `Copula`. The namespace
`ProbabilityTheory.Copula.RankRegion` provides a common API for all ten
pairs among Spearman's rho, Kendall's tau, Blomqvist's beta, Spearman's
footrule, and Gini's gamma. It also exposes the exact xi–beta region.

**All ten pairs have complete exact-region theorems.** An exact-region theorem proves both that every copula
satisfies the bounds and that every point satisfying them is attained by
an actual `Copula 2`. All statements include singular copulas.

## Coverage

| Pair | Status | Public theorem or development |
| --- | --- | --- |
| Footrule–tau | Exact | `attainable_footrule_tau_iff` |
| Gamma–tau | Exact | `attainable_gamma_tau_iff` |
| Footrule–gamma | Exact | `attainable_footrule_gamma_iff` |
| Beta–rho | Exact | `attainable_beta_rho_iff` |
| Beta–tau | Exact | `attainable_beta_tau_iff` |
| Beta–footrule | Exact | `attainable_beta_footrule_iff` |
| Beta–gamma | Exact | `attainable_beta_gamma_iff` |
| Rho–tau | Exact | `attainable_rho_tau_iff` |
| Rho–footrule | Exact | `attainable_footrule_rho_iff` |
| Rho–gamma | Exact | `attainable_gamma_rho_iff` |
| Xi–beta | Exact | `attainable_xi_beta_iff` |

For Chatterjee's directional coefficient \(x=\xi\) and Blomqvist's \(b=\beta\),
`attainable_xi_beta_iff` proves the complete region
\(0\le x\le1,\ -1\le b\le1,\ |b|^3\le2x\).
The proof includes the sharp lower boundary, the upper fibre endpoint, and
every point between them. Xi is directional: it is coordinate 1 given coordinate 0.

The exact statements are collected in
[`Copula.Rank.Region`](../Copula/Rank/Region.lean).

## Conventions and exact formulas

Write \(b=\beta\), \(p=\phi\) (footrule), \(g=\gamma\),
\(t=\tau\), and \(r=\rho\). Footrule has range
\([-1/2,1]\); the other four coefficients have range \([-1,1]\).
This is the population footrule normalization in the
[rank coefficient guide](rank-coefficients.md).

Each row below is an **if and only if** characterization. The interval
restriction in the second column is part of the theorem.

| Coordinates | First coordinate | Bounds on the second coordinate |
| --- | --- | --- |
| \((p,t)\) | \(-1/2\le p\le1\) | \(4p/3-1/3\le t\le2p/3+1/3\) |
| \((g,t)\) | \(-1\le g\le1\) | \(\max(2g/3-1/3,2g-1)\le t\le\min(2g/3+1/3,2g+1)\) |
| \((p,g)\) | \(-1/2\le p\le1\) | \(4p/3-1/3\le g\le\min(4p/3+1/6,2p/3+1/3)\) |
| \((b,r)\) | \(-1\le b\le1\) | \(3(1+b)^3/16-1\le r\le1-3(1-b)^3/16\) |
| \((b,t)\) | \(-1\le b\le1\) | \((1+b)^2/4-1\le t\le1-(1-b)^2/4\) |
| \((b,p)\) | \(-1\le b\le1\) | \(3(1+b)^2/16-1/2\le p\le1-3(1-b)^2/8\) |
| \((b,g)\) | \(-1\le b\le1\) | \(3(1+b)^2/8-1\le g\le1-3(1-b)^2/8\) |

```lean
import Copula.Rank.Region

open ProbabilityTheory.Copula.RankRegion

example : (0, 13 / 16) ∈ attainable .beta .rho := by
  rw [attainable_beta_rho_iff]
  norm_num

example : (13 / 16, 0) ∈ attainable .rho .beta := by
  rw [mem_attainable_swap, attainable_beta_rho_iff]
  norm_num

example : (-1 / 2, 0) ∉ attainable .footrule .gamma := by
  rw [attainable_footrule_gamma_iff]
  norm_num
```

`attainable a b` is the image of actual copulas in the stated coordinate
order. `mem_attainable_iff` exposes the existential copula witness.
`mem_attainable_swap` reverses the coordinates. Merely defining this set
does not establish its boundary.

## Proofs and witnesses

`TauFootrule` formalizes the diagonal argument of Kokol Bukovšek–Stopar,
applying it directly to copula measures. `TauGamma` uses their reflection
reduction and ordinal-sum boundary families. `FootruleGamma` proves the
quadrilateral bounds with absolute moments and fills its boundary with
mixtures.

`BetaBounds` proves the quadratic fixed-median bounds using diagonal
envelopes and tent integrals. `RhoBeta` proves the cubic bounds with a
squared-displacement certificate and median quadrant probabilities.
`Centered` supplies ordinal sums with equal comonotonic edge blocks.
In `Beta`, a centered half-turn simultaneously attains all four upper
boundaries, and its reflection supplies the lower boundaries.

Mixtures preserve rho, beta, footrule, and gamma affinely. Tau varies
continuously, but is generally quadratic in the mixture weight.
`fixed_coefficient_intermediate` therefore uses the intermediate value
theorem to fill each fixed-coordinate interval, including intervals of
tau values. It does not assume tau is affine or its regions are convex.

The proofs use only this package and its existing mathlib dependency.
[`CopulaTest.RankRegion`](../CopulaTest/RankRegion.lean) checks boundary
points, an interior point, exclusions, coordinate reversal, and imported
contact points. Transitive axiom reports for all ten exact theorems use
only `propext`, `Classical.choice`, and `Quot.sound`.

## The exact rho–footrule boundary

For \(-1/2\le p\le1\), the sharp lower boundary is
\[
r_{\min}(p)=-1+2\left(\sqrt{\frac{1+2p}{3}}\right)^3.
\]
The upper boundary consists of the endpoint \((1,1)\) and the following
polynomial arcs. For each integer \(N\ge1\), let
\(L=1/(2N)\), \(R=1/(2(N+1))\), and \(0\le v\le L-R\).

- Right half: \(m=R+N(N+1)v^2\) and
  \(q=R^2+2N(N+1)Rv^2+\frac23N(N+1)v^3\).
- Left half: \(m=L-N(N+1)v^2\) and
  \(q=L^2-2N(N+1)Lv^2+\frac23N(N+1)v^3\).

In both cases \((p,r_{\max})=(1-3m,1-6q)\).
The theorem `attainable_footrule_rho_iff` uses this parametrization through
`RhoFootrule.UpperParameter`. Its definitions are arithmetic; they do not
quantify over copulas or a variational optimum. The proof establishes
coverage of every \(p\), uniqueness at junctions, global optimality,
boundary attainment, and every intermediate rho value.

`UpperSpline` supplies the globally feasible periodic potential.
`UpperRightOptimal` and `UpperLeftOptimal` verify the finite path mixtures,
their uniform marginals, their moments, and equality in the dual bound.
`Lower` supplies the complementary sharp inequality and its centered
copula witnesses.

## The exact rho–gamma boundary

The upper boundary is parametrized by auxiliary displacement certificates.
For their parameters \(s,c,m,q\), set
\[
A=\frac{s+\sqrt{s^2+2c}}2,\qquad a=\frac A{1+A},\qquad z=\frac1{1+A}.
\]
The coordinates are
\[
g=1-2a^2-z^2m,\qquad r_{\max}=1-2a^3-\frac32z^3q.
\]
RhoGamma.UpperParameter includes the two endpoints, the half-shift branch
\(s\ge1,\ c=3/8-s/2,\ m=1/2,\ q=1/4\), and the left and right auxiliary
families used for rho–footrule. All coordinates are explicit arithmetic
expressions. Reflection gives the lower boundary.

The theorem attainable_gamma_rho_iff proves membership exactly when gamma
is in \([-1,1]\) and rho lies between the corresponding boundary values.
Coverage proves every gamma coordinate is covered, including the limiting
endpoints. GluedCertificate proves global dual feasibility and equality
for actual copula measures; GluedMoments computes their coefficients.
The proof fills all intermediate points by mixtures.

## The exact rho–tau boundary

The Schreyer–Paulin–Trutschnig lower boundary consists of \((-1,-1)\)
and the arcs below, with coordinates ordered as \((t,r)=(\tau,\rho)\).
For every integer \(n\ge0\) and \(s\in[0,1]\),
\[
t_n(s)=-1+\frac2{n+2}+\frac{2s^2}{(n+1)(n+2)},
\]
\[
r_n(s)=-1+\frac2{(n+2)^2}
+\frac{6s^2}{(n+1)(n+2)^2}
-\frac{2ns^3}{(n+1)^2(n+2)^2}.
\]
The upper boundary is its reflection through the origin.
`attainable_rho_tau_iff` characterizes membership using these
arithmetic parameters (`RhoTau.LowerParameter`). Equivalently,
if \(\Phi(t_n(s))=r_n(s)\) and \(\Phi(-1)=-1\), then
\[
-1\le t\le1,\qquad \Phi(t)\le r\le-\Phi(-t).
\]

The proof follows the finite permutation reduction in Section 4 of
Schreyer–Paulin–Trutschnig. `PowerSums` proves the symmetric
minimum; `SparseVariations` and `FourVariations` eliminate
the forbidden patterns; `AdjacentSwap` handles the remaining
nonendpoint case. The swap argument redistributes the two swapped weights
to preserve the inversion statistic exactly. `FiniteReduction.finite_sharp_bound`
then proves the sharp inequality for every finite weighted permutation.

`Quantization` and `GridMoments` transfer this inequality to
every copula using finite grid distributions and dominated convergence.
Uniform marginals exclude coordinate ties; `GridCollisions`
proves that the diagonal correction terms vanish.
`BoundaryFunction` proves continuity and ordering across all arc
junctions and at the limiting endpoint. `Universal` proves the
sharp bound for arbitrary copulas. Finally, `Exact` uses reflection
and continuity of tau along mixtures at fixed rho to attain every interior
point. The proof includes singular copulas and does not assume a density.

## Imported developments

The rho–footrule and rho–gamma proofs were adapted from
[Corrram/lean-verifications](https://github.com/Corrram/lean-verifications/tree/9e144da5e0d8e2b59dadf9cef090947cb2220313)
at commit `9e144da5e0d8e2b59dadf9cef090947cb2220313` (Apache 2.0).
Each ported file records its original module. Imports and namespaces were
adapted, and unused helpers were omitted; no dependency on that repository
is required. These are the checked portions of the two developments listed
on the [source papers page](https://corrram.github.io/lean-verifications/papers/).

## Mathematical references

- D. Kokol Bukovšek and N. Stopar,
  [*On the exact regions determined by Kendall's tau and other concordance measures*](https://link.springer.com/article/10.1007/s00009-023-02350-0)
  (2023), Theorems 4 and 6: tau–footrule and tau–gamma.
- D. Kokol Bukovšek, T. Košir, B. Mojškerc, and M. Omladič,
  [*Spearman's footrule and Gini's gamma: Local bounds for bivariate copulas and the exact region with respect to Blomqvist's beta*](https://arxiv.org/abs/2009.06221)
  (2021), Theorem 11: beta–footrule and beta–gamma.
- D. Kokol Bukovšek and B. Mojškerc,
  *On the exact region determined by Spearman's footrule and Gini's gamma*,
  J. Comput. Appl. Math. **410** (2022), 114212. Its pairwise result is also
  stated as Proposition 2.1 in their
  [*The exact region determined by Blomqvist's beta, Spearman's footrule and Gini's gamma*](https://dirros.openscience.si/Dokument.php?id=33288&lang=eng),
  J. Comput. Appl. Math. **473** (2026), 116861. Proposition 2.2 records the
  beta–footrule and beta–gamma bounds; Section 2 recalls the classical
  beta–rho and beta–tau results.
- M. Schreyer, R. Paulin, and W. Trutschnig,
  [*On the exact region determined by Kendall's tau and Spearman's rho*](https://www.trutschnig.net/p22.pdf),
  J. R. Stat. Soc. B **79** (2017), 613–633. The prototype formulas,
  finite extremal reduction, universal sharp bounds, and full exact-region
  theorem are formalized.
