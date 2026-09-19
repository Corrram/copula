# Rank dependence

Throughout this chapter, $C$ is a **bivariate** copula, $(U,V)\sim C$, and
$K_C(u,t)$ is a version of $\mathbb P(V\leq t\mid U=u)$.
These are population coefficients. No sample-ranking procedure or numerical
estimator is implicit in the definitions.

## Six coefficients

| Coefficient | Definition | Range |
| --- | --- | --- |
| Spearman's rho | $\rho(C)=12\int uv\,dC(u,v)-3$ | $[-1,1]$ |
| Kendall's tau | $\tau(C)=4\int C(u,v)\,dC(u,v)-1$ | $[-1,1]$ |
| Spearman's footrule | $\phi(C)=6\int_0^1 C(t,t)\,dt-2$ | $[-\tfrac12,1]$ |
| Gini's gamma | $\gamma(C)=4\int_0^1[C(t,t)+C(t,1-t)]\,dt-2$ | $[-1,1]$ |
| Blomqvist's beta | $\beta(C)=4C(\tfrac12,\tfrac12)-1$ | $[-1,1]$ |
| Chatterjee's xi | $\xi(C)=6\int_0^1\int_0^1 K_C(u,t)^2\,du\,dt-2$ | $[0,1]$ |

The footrule convention is the normalized population copula functional.
Chatterjee's xi measures dependence of the **second coordinate on the first**;
transposing the copula reverses that direction.

??? info "Formal definitions of rho, tau, footrule, gamma, and beta"
    {{ lean:rho }}
    {{ lean:tau }}
    {{ lean:footrule }}
    {{ lean:gamma }}
    {{ lean:beta }}

For the full range proofs and conditional-kernel definition of xi, see the
[rank API guide](../rank-coefficients.md).

## Benchmarks

| Copula | $\rho$ | $\tau$ | $\phi$ | $\gamma$ | $\beta$ | $\xi$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Independence $\Pi$ | 0 | 0 | 0 | 0 | 0 | 0 |
| Comonotonicity $M$ | 1 | 1 | 1 | 1 | 1 | 1 |
| Countermonotonicity $W$ | −1 | −1 | −1/2 | −1 | −1 | 1 |

Both $V=U$ and $V=1-U$ determine the second coordinate completely. That is
why xi equals one in both cases, although their concordance signs differ.

## What do extreme values identify?

!!! theorem "Extremes of Spearman's rho"

    $$
    \rho(C)=1\iff C=M,\qquad
    \rho(C)=-1\iff C=W.
    $$


{{ lean:rho-max }}
{{ lean:rho-min }}

Kendall's tau has analogous equality cases; for example:

$$
\tau(C)=1\iff C=M.
$$


{{ lean:tau-max }}

Maximal beta does not characterize $M$. It characterizes equal-split ordinal
sums, whose two components can vary. The
[ordinal-sum chapter](ordinal-sums.md#maximal-beta) explains this distinction.

## Detecting independence

!!! theorem "Xi vanishes exactly at independence"
    For every bivariate copula, including singular ones,

    $$\xi(C)=0\iff C=\Pi.$$

{{ lean:xi-zero }}

Zero rho or zero tau alone does not characterize independence. Under
positive quadrant dependence, however, zero rho does:

!!! theorem "Zero rho in the PQD class"
    If $C(u,v)\geq uv$ for every $(u,v)\in I^2$, then

    $$\rho(C)=0\iff C=\Pi.$$

{{ lean:pqd-zero }}

The [rank guide](../rank-coefficients.md) also describes the NQD analogues,
Kendall's concordance-probability interpretation, reflection identities,
mixture formulas, and the remaining equality cases.
