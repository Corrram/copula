# Copula families

A family supplies a parameterized dependence model. A closed formula alone
does not establish that it is a copula: the admissible parameter range and
the boundary values matter. The library's constructors carry the required
parameter proofs.

## Farlie–Gumbel–Morgenstern

!!! theorem "FGM formula and admissible parameters"
    For $-1\leq\theta\leq1$,

    $$
    C_\theta(u,v)=uv+\theta uv(1-u)(1-v),\qquad (u,v)\in I^2,
    $$


    is a copula. At $\theta=0$ it is independence.

{{ lean:fgm }}

This family is a useful example of a model whose parameter controls the
sign of dependence but cannot reach the full range of rank correlations:

$$
\rho(C_\theta)=\frac{\theta}{3},\qquad
\tau(C_\theta)=\frac{2\theta}{9}.
$$


{{ lean:fgm-rho }}
{{ lean:fgm-tau }}

The library also proves that FGM is stochastically increasing exactly when
$\theta\geq0$.

{{ lean:fgm-si }}

## Clayton with positive parameter

!!! theorem "Clayton CDF"
    For $\theta>0$ and positive coordinates $u_i\in(0,1]$,

    $$
    C_\theta(u_1,\ldots,u_d)
    =\left(\sum_{i=1}^d u_i^{-\theta}-d+1\right)^{-1/\theta}.
    $$


    If a coordinate is zero, the CDF is zero.

{{ lean:clayton }}

The positive-parameter construction works in every finite dimension. The
bivariate negative-parameter construction is separate; see the
[family coverage guide](../families.md) for its exact range and API.

## Gumbel–Hougaard

!!! theorem "Gumbel CDF"
    For $\theta\geq1$ and $u,v\in(0,1]$,

    $$
    C_\theta(u,v)=\exp\left(-\left[(-\log u)^\theta+
    (-\log v)^\theta\right]^{1/\theta}\right).
    $$


    On the lower boundary its value is zero. The case $\theta=1$ is
    independence.

{{ lean:gumbel }}

Gumbel belongs to both the Archimedean and extreme-value classes. Its
extreme-value identity is, for $t>0$,

$$
C_\theta(u^t,v^t)=C_\theta(u,v)^t.
$$


{{ lean:gumbel-ev }}

## Beyond these examples

The package also contains Gaussian and Student-t constructions, other
elliptical scale mixtures, further Archimedean families, asymmetric
extreme-value examples, and singular mixtures. Properties are proved
family by family; a constructor's presence does not imply that every known
rank formula or ordering theorem has been formalized.

The [family guide](../families.md) lists the implemented APIs. The
[Ansari–Rockel coverage table](../ansari-rockel.md) records parameter domains,
closed-form expressions, proved properties, and remaining gaps against the
paper's family catalogue.
