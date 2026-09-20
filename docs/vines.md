# Vine copulas

`Copula.Vine` constructs **C-vine, D-vine, and regular-vine copulas in every
finite dimension**, with either fixed or conditioning-dependent pair copulas.
The construction uses probability kernels and generalized conditional quantiles.
It accepts singular pair copulas and does not require densities or strictly
increasing conditional distributions.

The output is an ordinary `Copula d`, with proved uniform coordinate marginals.
Every attachment also preserves the complete law of the previously constructed
coordinates. Dimension zero and singleton dimensions are supported.

## Structure and simplification are separate

| Structure | Construction | API |
| --- | --- | --- |
| C-vine | Each tree is a star around successive roots | `RVineStructure.cVine`, `Copula.cVine` |
| D-vine | A chain, with interval conditioning sets in subsequent trees | `RVineStructure.dVine`, `Copula.dVine` |
| R-vine | Mixed attachment paths through nested coordinate clusters | `RVineStructure.ofOrder`, `RVineStructure.toCopula` |

For each structure, `toCopula` accepts measurable families of pair copulas.
The `simplified` constructor takes constant bivariate copulas instead.
C- and D-vines are special cases of the regular-vine constructor, rather than
coordinate permutations of a single C-vine construction.

## Variable order and regular-vine paths

`RVineStructure.ofOrder order paths` takes a permutation describing the order
in which variables are added. At each level, `false` selects the existing
cluster's left parent and `true` selects its right parent. The new higher-tree
edge shares that parent with its two endpoint clusters, satisfying proximity.
Missing path choices default to left; entries after reaching a leaf are unused.

Choosing left throughout gives a C-vine. Choosing right throughout gives a
D-vine. Mixed choices give other regular vines. `firstTree` lists the
unconditional edges; `edges` lists all triples `(a, b, conditioningSet)`.
The orientation matters: coordinate 0 of the supplied pair copula corresponds
to `a`, and coordinate 1 corresponds to `b`.

For four variables in natural order, the complete tables are:

| Tree | C-vine edges | D-vine edges |
| --- | --- | --- |
| First | `01`, `02`, `03` | `01`, `12`, `23` |
| Second | `12;0`, `13;0` | `02;1`, `13;2` |
| Third | `23;01` | `03;12` |

A tested five-variable mixed-path example has first-tree edges
`01`, `12`, `23`, `14`. Its vertex degrees are 3, 2, 1, 1, 1, so it is neither
a star nor a chain under any relabeling. All ten pair edges are present.

{{ lean:rvine-valid }}

## Public constructors

```lean
import Copula.Vine

open ProbabilityTheory
open scoped unitInterval

noncomputable section

-- Measurable conditional pair families.
example (F : Copula.Vine.PairFamilies 4) : Copula 4 :=
  Copula.cVine (Equiv.refl _) F

example (F : Copula.Vine.PairFamilies 4) : Copula 4 :=
  Copula.dVine (Equiv.refl _) F

example (S : Copula.RVineStructure 5) (F : Copula.Vine.PairFamilies 5) : Copula 5 :=
  S.toCopula F

-- A simplified D-vine: one fixed copula for each oriented conditional pair.
example (pairs : Fin 4 → Fin 4 → Finset (Fin 4) → Copula 2) : Copula 4 :=
  (Copula.RVineStructure.dVine (Equiv.refl _)).simplified pairs
```

`PairFamilies d` assigns a `Family (Fin d → I) 2` to each triple `(a, b, S)`.
Only entries belonging to the selected structure are used. The family is
evaluated on the actual conditioning coordinates in `S`, with zeros in all
other positions. A family cannot inspect either conditioned endpoint or a
variable outside its conditioning set.

`Family.const C` supplies a simplified pair. `Family.ofCopulas` accepts a
copula-valued function together with measurability of its probability laws.
`Family.comap` changes the parametrization, and `Family.piecewise` selects
families on a measurable set. For example:

```lean
noncomputable def switchingPair (threshold : I) : Copula.Family (Fin 3 → I) 2 :=
  Copula.Family.piecewise {x | x 0 ≤ threshold}
    (measurableSet_le (measurable_pi_apply 0) measurable_const)
    (Copula.Family.const (Copula.comonotonic 2))
    (Copula.Family.const Copula.countermonotonic)
```

Assigning this family to `(1, 2, {0})` makes the second-tree pair of a
three-variable C-vine depend on the observed value of its root. The tests
check both branches, including these singular pair copulas.

## Conditional gluing and proved marginal consistency

Suppose $L$ is the law on coordinates $(a,S)$ and $R$ is the law on $(b,S)$,
with common $S$-marginal $D$. Given $X_S=x$, draw $(U,V)$ from the supplied
conditional copula $C_{ab;S}(x)$ and set

$$
X_a=Q_{a\mid S}(x,U),\qquad X_b=Q_{b\mid S}(x,V).
$$

`Vine.glue` constructs this law. The generalized quantiles include endpoints
and atoms. The result has exactly the original $(a,S)$ and $(b,S)$ marginals.
In the regular-vine builder, these common-marginal conditions are proved
recursively; callers do not supply compatibility proofs for their pair families.

With an empty conditioning set, projecting the join onto its two endpoints
recovers the supplied pair copula exactly. The tests also check this through
the complete two-variable regular-vine constructor.

{{ lean:rvine-pair }}

{{ lean:rvine-glue-left }}

{{ lean:rvine-glue-right }}

`Vine.glueProbability_apply` gives the event-probability integral against
$D(dx)C_{ab;S}(x)(du,dv)$, with the conditional quantile map inside the event.
The family is evaluated before integration, retaining its dependence on the
conditioning values.

{{ lean:rvine-probability }}

`Vine.Realization` records the ancestral marginal identities, and
`Vine.modelOfList_cons_marginal` proves that adding a variable preserves the
entire joint law of all earlier variables.

{{ lean:rvine-extension }}

Conditional distributions use fixed versions; changes on null sets do not
change the resulting law. With atomic conditional distributions, the conditional
copula need not be unique. The chosen pair family specifies a quantile coupling;
the implementation does not assert uniqueness of that family.

## Existing simplified C-vine API

`CVine.nil`, `singleton`, `pair`, `triple`, `cons`, `ofPairs`, and `independent`
remain available. They provide the earlier direct recursive C-vine construction.
Its root-pair marginals and the CDF formula

$$
C(u_0,\ldots,u_d)=\int_0^{u_0}
D\bigl(H_{A_0}(r,u_1),\ldots,H_{A_{d-1}}(r,u_d)\bigr)\,dr
$$

are proved, where $H_A$ is the conditional CDF of a bivariate input.

{{ lean:vine-pairs }}

{{ lean:vine-cdf }}

The all-independence identity `CVine.toCopula_independent` belongs to this
direct API. A formal identification between it and the new general C-vine
builder, and general R-vine density factorization and independence formulas,
remain further results to prove.

{{ lean:vine-independence }}

## Scope

All three structure classes and both constant and conditioning-dependent pairs
are supported as noncomputable mathematical probability laws. Conventional
R-vine matrix import/export, statistical fitting, and executable numerical
simulation are not implemented. Structure validity is proved for the path
construction; a formal equivalence with every conventional tree-sequence or
matrix representation is not claimed.

For standard structure terminology, see
[VineCopula's R-vine documentation](https://tnagler.github.io/VineCopula/reference/RVineMatrix.html)
and [vinecopulib's structure API](https://vinecopulib.github.io/vinecopulib/classvinecopulib_1_1_r_vine_structure.html).
The declarations above specify the exact formal coverage.
