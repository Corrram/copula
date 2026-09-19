# What is a copula?

A copula describes dependence after the marginal distributions have been
made uniform. Write $I=[0,1]$. In the library, a $d$-dimensional copula is a
probability measure $\mu_C$ on $I^d$ such that every coordinate has the uniform
distribution on $I$.

{{ lean:copula }}

Its distribution function is derived from that measure:

$$
C(u_1,\ldots,u_d)
=\mu_C\{x:x_i\leq u_i\text{ for every }i\}.
$$


{{ lean:cdf }}

The notation $C$ refers to the CDF in mathematical prose; Lean distinguishes
the bundled object `C`, its measure `C.toMeasure`, and the function `C.cdf`.
The measure representation covers singular copulas as well as copulas with
densities.

## The classical viewpoint

A classical copula CDF is grounded, has uniform one-dimensional margins, and
has nonnegative alternating increments over coordinate rectangles. In two
dimensions, the rectangle condition is

$$
C(b,d)-C(a,d)-C(b,c)+C(a,c)\geq0
\qquad(a\leq b,\ c\leq d).
$$


The library constructs a measure-based copula from these classical conditions
and proves that its CDF is the original function.

{{ lean:classical }}

## Every copula is bounded

!!! theorem "Fréchet–Hoeffding bounds"
    For $d\geq1$ and $u\in I^d$,

    $$
    \max\left(0,\sum_{i=1}^d u_i-d+1\right)
    \leq C(u)\leq\min_{1\leq i\leq d}u_i.
    $$


{{ lean:lower-bound }}
{{ lean:upper-bound }}

In two dimensions these bounds are themselves copulas:
$W(u,v)=\max(0,u+v-1)$ and $M(u,v)=\min(u,v)$.
In dimensions above two, the displayed lower-bound function is generally
not a copula. The formal theorems also cover dimension zero, using the
empty-infimum convention; the empty-dimensional CDF is one.

## Continuity needs no extra hypothesis

!!! theorem "Lipschitz regularity"
    Every copula satisfies

    $$
    |C(u)-C(v)|\leq\sum_{i=1}^d |u_i-v_i|.
    $$


    Thus every copula CDF is continuous, even if its measure has no density.

{{ lean:lipschitz }}

This is a Lipschitz constant of one for the sum metric. Lean's default metric
on finite products is the maximum metric, for which the corresponding bound
has constant $d$.

## Three reference examples

For a bivariate copula, the main benchmarks are

$$
\Pi(u,v)=uv,\qquad M(u,v)=\min(u,v),\qquad
W(u,v)=\max(0,u+v-1).
$$


They represent independent coordinates, equal uniform coordinates, and
coordinates $(U,1-U)$, respectively.

{{ lean:independence }}
{{ lean:comonotonic }}
{{ lean:countermonotonic }}

Continue with [Sklar's theorem](sklar.md) to connect these objects to arbitrary
joint distributions, or [families](families.md) for parameterized examples.
