# Sklar's theorem

Let $X=(X_1,\ldots,X_d)$ have an arbitrary probability law on $\mathbb R^d$.
Write $H$ for its joint CDF and $F_i$ for its marginal CDFs.

!!! theorem "Existence"
    There is a copula $C$ such that, for every $x\in\mathbb R^d$,

    $$
    H(x_1,\ldots,x_d)=C(F_1(x_1),\ldots,F_d(x_d)).
    $$


    The marginal distributions may have atoms.

{{ lean:sklar }}

The marginals specify the separate distributions; the copula supplies a
dependence structure that reproduces the joint CDF.

## Precisely where is it unique?

!!! theorem "Uniqueness on marginal ranges"
    If $C$ and $D$ give the same Sklar factorization, then

    $$
    C(u)=D(u)\qquad
    \text{for }u\in\prod_{i=1}^d\operatorname{range}(F_i).
    $$


{{ lean:sklar-ranges }}

With discontinuous margins, the marginal CDFs skip intervals. The joint law
therefore does not determine the copula at every point of the unit cube.

!!! theorem "Global uniqueness with continuous marginals"
    If every $F_i$ is continuous, there is exactly one copula $C$ giving the
    factorization above.

{{ lean:sklar-unique }}

Strict monotonicity of the marginal CDFs is not required. Their ranges are
dense enough, and copula CDFs are continuous, so agreement on the product of
the ranges extends to the whole cube.

## How the construction works

For continuous marginals, the probability integral transform sends
$X_i$ to $F_i(X_i)$, which is uniform. This directly gives the copula law.
For arbitrary marginals, the formal construction uses quantile lifting,
including randomized inverses where atoms prevent a deterministic uniform
transform. See the [design guide](../design.md) for the underlying modules.

The existence and uniqueness results concern probability laws. They do not
assume a density, a particular copula family, or invertibility of every
marginal CDF.
