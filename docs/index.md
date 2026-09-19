# Copulas, with the proofs attached

Read the mathematics in familiar notation, then follow any featured result to
its exact Lean statement and proof. This is the handbook for **copula**, an
independent Lean 4 library built on mathlib.

[Read the handbook](handbook/foundations.md){ .md-button .md-button--primary }
[Browse the Lean API](api-guide.md){ .md-button }

## A theorem to start with

!!! theorem "When does a copula split into two diagonal blocks?"
    Let $C$ be a bivariate copula and fix $0<a<1$. Then

    $$
    C(a,a)=a
    \quad\Longleftrightarrow\quad
    \exists!\,(D,E)\text{ copulas such that }C=D\oplus_a E.
    $$


    The components are unique **for this fixed split**. A copula can have
    several possible split points.

{{ lean:ordinal-unique }}

The [ordinal-sum chapter](handbook/ordinal-sums.md) explains the construction,
its probability interpretation, and consequences for rank dependence.

## Choose a topic

<div class="grid cards" markdown>

- **Foundations**

    Probability measures, distribution functions, Fréchet bounds, and continuity.

    [Start with copulas](handbook/foundations.md)

- **Sklar's theorem**

    Separate a joint distribution into its marginal laws and dependence structure.

    [Existence and uniqueness](handbook/sklar.md)

- **Families**

    Familiar formulas, parameter restrictions, and links to proved properties.

    [Explore examples](handbook/families.md)

- **Rank dependence**

    Six coefficients, their meanings, and what their extreme values determine.

    [Read the rank chapter](handbook/rank.md)

- **Orders and positive dependence**

    Lower orthant order, Schur order, SI, LTD, RTI, and PQD.

    [Compare dependence](handbook/dependence.md)

- **Ordinal sums**

    Construct copulas from blocks and recover their unique components at a cut.

    [Decompose a copula](handbook/ordinal-sums.md)

</div>

## How to read this site

The **handbook** is a curated mathematical explanation. Its formal-statement
links lead to the **API reference**, generated from the Lean declarations.
Source links point to the exact library revision used for the site build.
Lean checks the formal proofs; the prose is an explanation of those results.

The [theorem index](theorem-index.md) lists the featured declarations. The API
has a separate search covering the library and its documented dependencies.
The [coverage guides](families.md) record what is implemented and what remains
open; this handbook is not a claim of complete coverage of copula theory.

## Use the library

The current release uses **Lean and mathlib v4.34.0**. In `lakefile.toml`:

```toml
[[require]]
name = "copula"
git = "https://github.com/Corrram/copula.git"
rev = "v0.1.0"
```

Run `lake update`, then `import Copula` or a focused module. This site follows
`main`; its revision is shown on each handbook page. When citing a result,
record the exact commit used in your project.
