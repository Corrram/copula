# Ordinal sums and diagonal cuts

An ordinal sum places one copula in a lower diagonal block and another in
an upper diagonal block. Let $D,E$ be bivariate copulas and $0<a<1$. Then

$$
(D\oplus_a E)(u,v)=
\begin{cases}
aD(u/a,v/a), & u,v\leq a,\\
a+(1-a)E\!\left(\frac{u-a}{1-a},\frac{v-a}{1-a}\right), & u,v\geq a,\\
\min(u,v), & \text{otherwise}.
\end{cases}
$$


The formulas agree on the block boundaries. Probabilistically, the lower
block has mass $a$ and the upper block has mass $1-a$; within a chosen block,
the corresponding component is affinely rescaled.

## Recognizing an ordinal sum

!!! theorem "Nelsen's binary converse ordinal-sum theorem"
    Let $C$ be a bivariate copula and fix $0<a<1$. Then

    $$C(a,a)=a\iff\exists!\,(D,E)\text{ such that }C=D\oplus_a E.$$

{{ lean:ordinal-unique }}

The component formulas are explicit:

$$
D(s,t)=\frac{C(as,at)}a,\qquad
E(s,t)=\frac{C(a+(1-a)s,a+(1-a)t)-a}{1-a}.
$$


The construction proves that these are copulas and that reassembling them
recovers $C$.

{{ lean:ordinal-reconstruct }}

Uniqueness concerns the pair at the **chosen split**. It does not assert
that the split itself is unique: $M$ has a cut at every interior point.

## The cut as a probability statement

!!! theorem "Threshold disagreement"
    If $(U,V)\sim C$, then for every $a\in I$,

    $$
    \mathbb P\bigl(\mathbf1_{\{U\leq a\}}\ne\mathbf1_{\{V\leq a\}}\bigr)
    =2\bigl(a-C(a,a)\bigr).
    $$


{{ lean:ordinal-disagreement }}

Thus $C(a,a)=a$ means that both coordinates fall on the same side of the
threshold almost surely. No density is needed, and this identity includes
$a=0$ and $a=1$.

If $C$ is NQD, then $C(a,a)\leq a^2<a$ for interior $a$. Consequently an
NQD copula cannot have a nontrivial binary ordinal-sum decomposition.

{{ lean:ordinal-nqd }}

## Rank formulas

The formulas below hold for all $a\in[0,1]$, with the degenerate sums
$D\oplus_0E=E$ and $D\oplus_1E=D$:

$$
\tau(D\oplus_aE)=1-a^2(1-\tau(D))-(1-a)^2(1-\tau(E)),
$$


$$
\rho(D\oplus_aE)=1-a^3(1-\rho(D))-(1-a)^3(1-\rho(E)),
$$


$$
\phi(D\oplus_aE)=1-a^2(1-\phi(D))-(1-a)^2(1-\phi(E)).
$$


{{ lean:ordinal-tau }}
{{ lean:ordinal-rho }}
{{ lean:ordinal-footrule }}

The quadratic and cubic weights differ because the coefficients integrate
different functions against different measures.

## Maximal beta

!!! theorem "An equal-split characterization"

    $$\beta(C)=1\iff\exists!\,(D,E)\text{ such that }C=D\oplus_{1/2}E.$$

{{ lean:ordinal-beta }}

This characterization allows many copulas beyond $M$. It also implies

$$\beta(C)=1\Longrightarrow\rho(C)\geq\tfrac12\quad\text{and}\quad\tau(C)\geq0.$$

{{ lean:beta-rho-bound }}
{{ lean:beta-tau-bound }}

The complete [ordinal-sum guide](../ordinal-sums.md) includes sharpness
examples, footrule bounds, beta $-1$, component recovery, and tail behavior.
Finite sums and countably many adjacent blocks with endpoints tending to
one now have proved constructors; see the guide for their hypotheses.
Arbitrary disjoint intervals with a residual comonotonic part and canonical
decomposition into indecomposable components remain future work.
