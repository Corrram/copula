# Orders and positive dependence

Different comparisons answer different questions. This chapter uses
bivariate copulas and the orientation **second coordinate given first**
for directional dependence properties.

## Lower orthant and concordance order

Lower orthant order compares the distribution functions pointwise:

$$
C\preceq_{\mathrm{lo}}D
\quad\Longleftrightarrow\quad
C(u,v)\leq D(u,v)\quad\text{for every }u,v\in I.
$$


Concordance order compares both lower-orthant and upper-orthant
probabilities. In two dimensions, these conditions coincide with the
pointwise comparison above.

{{ lean:concordance }}

!!! theorem "Strict monotonicity of rho among comparable copulas"
    If $C\preceq_{\mathrm{lo}}D$ and $C\ne D$, then

    $$\rho(C)<\rho(D).$$

{{ lean:order-strict }}

Comparability is essential. Rho is a single number and does not identify
an arbitrary copula among all copulas.

## Schur order through conditional CDFs

For $K_C(u,t)=\mathbb P(V\leq t\mid U=u)$, the library uses the convex-test
formulation

$$
C\preceq_{\mathrm{Schur}}D
\quad\Longleftrightarrow\quad
\int_0^1\psi(K_C(u,t))\,du
\leq\int_0^1\psi(K_D(u,t))\,du
$$


for every $t\in I$ and every continuous $\psi:\mathbb R\to\mathbb R$ that
is convex on $I$. Each conditional section has mean $t$.

!!! theorem "Independence is least"
    Every bivariate copula satisfies $\Pi\preceq_{\mathrm{Schur}}C$.

{{ lean:schur-least }}

!!! theorem "Xi respects Schur order"

    $$C\preceq_{\mathrm{Schur}}D\quad\Longrightarrow\quad\xi(C)\leq\xi(D).$$

{{ lean:schur-xi }}

Schur order is a preorder here: distinct copulas can be comparable in both
directions. For the exact conventions and the scope of the formalization,
see the [orders guide](../orders.md).

## Positive dependence implications

For each fixed $v$, the principal directional conditions are:

| Condition | Mathematical meaning |
| --- | --- |
| PQD | $C(u,v)\geq uv$ |
| LTD | $u\mapsto C(u,v)/u$ is nonincreasing on $(0,1]$ |
| RTI | $u\mapsto[1-u-v+C(u,v)]/(1-u)$ is nondecreasing on $[0,1)$ |
| SI | $u\mapsto C(u,v)$ is concave |

The SI row is the CDF-section characterization used by the library. Its
connection with monotone conditional laws is developed separately.

!!! theorem "Two paths from SI to PQD"

    $$
    \mathrm{SI}\Longrightarrow\mathrm{LTD}\Longrightarrow\mathrm{PQD},
    \qquad
    \mathrm{SI}\Longrightarrow\mathrm{RTI}\Longrightarrow\mathrm{PQD}.
    $$


{{ lean:si-ltd }}
{{ lean:ltd-pqd }}
{{ lean:si-rti }}
{{ lean:rti-pqd }}

Transposing the copula reverses the conditioning direction. Total positivity
of a CDF, a conditional kernel, and a density are separate predicates; the
[positive-dependence guide](../positive-dependence.md) states their proved
connections without identifying them by definition.
