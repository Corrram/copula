# Further standard copula results

Reference: Roger B. Nelsen, *An Introduction to Copulas*, second edition,
Springer, 2006, [publisher page and DOI](https://link.springer.com/book/10.1007/0-387-28678-0).
The following are independently written Lean proofs using the package's
probability-measure representation.

## Coverage map

| Topic in Nelsen | Formal module | Added results |
| --- | --- | --- |
| Exercise 2.8; §3.2.6, conditions (3.2.21) | `Copula.Diagonal` | Diagonal bounds, monotonicity, 2-Lipschitz regularity, endpoint values, and `δ = id ↔ C = M` |
| §3.2.2, binary ordinal-sum construction | `Copula.OrdinalSum` | Full split-parameter range, CDF and measure formulas, block probabilities, recovery, order, exchangeability, PQD and tail inheritance |
| Theorem 3.2.1 and the subsequent probability criteria | `Copula.OrdinalSum.Cut`, `Components`, `Decomposition` | Explicit component extraction, reconstruction and uniqueness at an interior cut; equivalent threshold and max/min events |
| §3.2.2 and §5.1, ordinal-sum rank calculations | `Copula.OrdinalSum.Rank`, `RankExamples` | Exact rho, tau, footrule and common-split Q formulas; sharp bounds and benchmark specializations |
| §3.2.6, order-statistic interpretation | `Copula.Diagonal` | Distribution functions of the coordinate maximum and minimum |
| §3.2.6, copulas with prescribed diagonal sections | `Copula.Diagonal.Construction`, `Bertino`, `Extremal`, `UpperBound` | Sufficiency of the diagonal conditions (`K_δ`); Bertino copula `B_δ` as the smallest copula with diagonal `δ`; `K_δ` as the largest exchangeable one; the quasi-copula bound `A_δ` (best possible for quasi-copulas, not for copulas); `δ` determines `C` iff `δ = id` |
| §3.2.5, copulas with quadratic sections | `Copula.Families.QuadraticSections` | `uv + ψ(v)u(1−u)` is a copula iff `ψ(0) = ψ(1) = 0` and `ψ` is 1-Lipschitz; quadratic vertical sections force this form; quadratic sections in both variables iff FGM |
| §2.6 | `Copula.Reflection.Bivariate` | Single-coordinate reflection formulas, survival copula, transpose and composition identities |
| §2.7 | `Copula.Symmetry` | Copula-level exchangeability and radial symmetry, CDF characterizations, mixtures and symmetrization |
| §5.1, symmetry properties of concordance | `Copula.Rank.Symmetry` | Transpose and survival invariance; single-reflection sign changes |
| §2.5 and §5.1, extremal dependence and concordance | `Copula.Support`, `Rank.Extrema`, `Rank.MedianExtrema` | Almost-sure characterizations of M/W; coefficient equality cases and nonuniqueness at median/footrule extrema |
| §5.1 and §5.2, ordering and quadrant dependence | `Copula.Order.StrictSpearman` | Strict rho comparison; zero rho or tau characterizes independence within PQD/NQD |
| §5.1, concordance function and Kendall's tau | `Copula.Rank.Concordance`, `ConcordanceProbability`, `KendallMixture` | Q, independent-pair probabilities, benchmark links, and quadratic mixture formulas |
| §5.1, Fréchet and Mardia coefficient examples | `Copula.Rank.FrechetKendall` | Tau, footrule, gamma and beta on the full parameter domains |
| §5.4, including the CDF formulas of Theorem 5.4.2 | `Copula.TailDependence` | Limits, range, uniqueness, reflection duality, order and mixture results, benchmark/family values |
| §4.1, Theorem 4.1.5 | `Copula.Archimedean.Associativity` | Commutativity, associativity `C(C(u,v),w) = C(u,C(v,w))` (strict and non-strict generators), invariance under `φ ↦ cφ` |
| §4.1 and §4.3, level curves, zero set, Theorem 4.3.2 | `Copula.Archimedean.LevelCurves` | Level curves `φ(u)+φ(v) = φ(t)`, convexity of `φ`, of the level curves and of the sets `{C ≥ t}`; zero set, strict generators iff `C > 0` on `(0,1]²`, zero threshold `φ(0)` of non-strict generators |
| §4.3, Theorems 4.3.3 and 4.3.4 (Kendall distribution function) | `Copula.Archimedean.Derivative`, `KendallDistribution`, `KendallCDF` | For generators with `C¹` inverse generator (strict or not): `K_C(t) = t − φ(t)/φ'(t)` on `(0,1]`, mass `K_C(0) = −φ(0)/φ'(0⁺)` of the zero set (`0` for strict, `1` for `W`, `1/θ` for family 2); conditional CDFs equal `∂₁C` a.e. simultaneously in `v` |
| §5.1, Corollary 5.1.4 and its examples | `Copula.Archimedean.KendallTau`, `KendallTauFamilies`, `KendallTauAMH`, `KendallTauFrank` | `τ = 1 + 4∫₀¹ φ(t)/φ'(t) dt` for `C¹` generators (strict or not), `τ_{φ^δ} = 1 + (τ_φ − 1)/δ`; Clayton `θ/(θ+2)`, Gumbel `1 − 1/θ`, AMH `1 − 2(θ + (1−θ)² log(1−θ))/(3θ²)`, BB1 `1 − 2/(δ(θ+2))`, families 2 (`1 − 2/θ`), 12 and 14; Frank as `1 + (4/θ)∫₀¹ (e^{θt} − 1) log((1 − e^{−θt})/(1 − e^{−θ})) dt` and in Debye form `1 − (4/θ)(1 − D₁(θ))` for `θ > 0` and `θ < 0` (`KendallTauFrankDebye`); from a differentiable generator `φ` (`KendallTauGenerator`): negative Clayton `θ/(θ+2)`, families 7, 8, 15, 16, 18 in closed form, Joe and families 9, 13, 19, 20 as explicit integrals (`KendallTauTable`, `KendallTauIntegral`) |
| §5.4, Corollary 5.4.3 | `Copula.Archimedean.TailDependence`, `TailFamilies` | `λ_L = lim ψ(2x)/ψ(x)` (strict), `λ_L = 0` (non-strict), `δ'(1⁻) = lim (1−ψ(2x))/(1−ψ(x))` and `λ_U = 2 − δ'(1⁻)`; `λ_U = 0` when `ψ'(0⁺)` is finite and nonzero |
| §4.2, Table 4.1 (all 22 one-parameter Archimedean families) | `Copula.Families.NelsenTable`, `Copula.Archimedean.Clamp`, see [nelsen-table-4-1.md](nelsen-table-4-1.md) | Generators, CDFs on the full parameter ranges, special and limiting cases, `λ_L = 0` for non-strict families; corrected CDF of family 22 |
| §5.3.1, measures of dependence based on distances to `Π` | `Copula.Measures.Bounds`, `Measures.Uniform`, `Measures.CDFDistanceBenchmarks` | `σ ≤ 1`, `Φ² ≤ 1`, `Φ²(M) = Φ²(W) = 1`, and `σ = 1 ↔ Φ² = 1 ↔ C ∈ {M, W}`; the `L∞` version `κ` with `\|β\| ≤ κ ≤ 1` and `κ = 1 ↔ \|β\| = 1`, `σ ≤ 3κ`, `Φ² ≤ (45/8) κ²` |
| §2.5, Theorem 2.5.4 (both directions) | `Copula.RandomVariable.Monotone`, `Copula.Distribution.RealQuantile` | With continuous marginals, `C = M` (resp. `W`) iff `Y = f(X)` a.s. with `f` nondecreasing (resp. nonincreasing) on a set carrying `X`; `f = G_Y ∘ F_X` (resp. `G_Y ∘ (1 − F_X)`) |
| §3.2, Theorem 3.2.3 | `Copula.QuasiCopula.PrescribedValue`, `PrescribedValueBest` | Bounds for copulas and quasi-copulas with `C(a,b) = θ`; both bounds are copulas (shuffles of `M`), hence best possible |
| §6.2, quasi-copulas | `Copula.QuasiCopula.Basic`, `Bivariate` | Definition (functional form), copulas are quasi-copulas, `W ≤ Q ≤ M`, sup/inf of copulas, characterization by boundary rectangles, a proper quasi-copula |
| §3.2.2, Definition 3.2.1 and Theorem 3.2.1 (general ordinal sums) | `Copula.OrdinalSum.General`, `GeneralProperties`, `GeneralDecomposition` | Ordinal sums over any family of pairwise disjoint open intervals (finite, countable, with gaps), `M` off the squares; CDF on the squares and off them, component recovery and uniqueness, `δ(t) = t` off the intervals, transpose/exchangeability, orthant order, PQD; finite, countable and binary constructors as instances; `C` is an ordinal sum w.r.t. the family iff `δ_C(t) = t` off the open intervals |
| §3.2.3, Theorem 3.2.2 (shuffles of `M` are dense) | `Copula.Shuffle.Weights`, `Shuffle.Density` | For every `C` and every grid, a straight shuffle of `M` with the same cell masses (hence equal to `C` at the grid vertices); `d∞(S_n, C) ≤ 2/n` on the uniform `n`-grid; straight shuffles (and all shuffles) of `M` are dense for the uniform metric |
| §4.1, Theorem 4.1.4 ("only if") and uniqueness of generators | `Copula.Archimedean.Converse`, `Copula.Archimedean.Uniqueness` | An Archimedean formula `ψ(φ(u)+φ(v))` (with `ψ` strictly decreasing where positive) is a copula iff `ψ` is convex (`ArchimedeanPregenerator.exists_copula_iff`), proved without continuity via nondecreasing increments; two generators give the same copula iff `φ₂ = cφ₁`, `c > 0` (Genest–MacKay; `BivariateGenerator.copula_eq_iff`) |
| §4.4, Theorem 4.4.2 and Corollary 4.4.3 (ordering via generators) | `Copula.Archimedean.Concordance`, `ConcordanceFamilies` | `C₁ ≤ C₂` iff `φ₁ ∘ ψ₂` is subadditive (strict `ψ₂`; `lowerOrthantLE_iff_subadditive`), concave suffices; PQD iff `ψ(x)ψ(y) ≤ ψ(x+y)` (strict), non-strict generators are never PQD, NQD iff `φ(uv) ≤ φ(u)+φ(v)`; Clayton increasing in `θ`; Table 4.1 families 9, 10 NQD, 13 PQD/NQD, 19, 20 PQD |
| §5.4, Corollary 5.4.3 applied to Table 4.1 | `Copula.TailDependence.NelsenTableUpper`, `NelsenTableLower` | `λ_U = 0` for families 7, 10, 11, 13, 16, 17, 22; `λ_L = 0` for 10, 13, 17; `λ_U = 2 − 2^{1/θ}` for 21 |
| §4.2, Table 4.1 limiting cases | `Copula.Families.NelsenTable.LimitsZero`, `LimitsInfinity` | `C₀ = Π` for families 11 and 22, `C_∞ = M` for 17 and 21; for family 17 the limit at `−∞` is `max(0, (uv+u+v−1)/2)` (family 7 at `θ = 1/2`), not `W` |

These are the precise formalized portions, not claims that every theorem in
the cited sections is implemented. The general random-variable versions of
the symmetry characterizations are not part of this addition.

## Diagonals and transformations

`C.diagonal t` is `C.cdf ![t,t]`. The necessary conditions on diagonal
sections (`IsDiagonalFunction`: `δ(1) = 1`, `0 ≤ δ(t) ≤ t`, `δ` nondecreasing
and `δ(t') − δ(t) ≤ 2(t' − t)`) are also sufficient:
`Diagonal.Construction` builds the Fredricks–Nelsen copula
`K_δ(u,v) = min(u, v, (δ(u)+δ(v))/2)` with diagonal `δ`
(`isDiagonalFunction_iff_exists_copula`). For a diagonal function `δ` with
gap `δ̂(t) = t − δ(t)`:

- `Diagonal.Bertino`: the Bertino copula
  `B_δ(u,v) = min(u,v) − min_{t ∈ [u∧v, u∨v]} δ̂(t)` is an exchangeable copula
  with diagonal `δ` and lies below every copula with diagonal `δ`
  (`bertinoCopula_cdf_le`), so it is the smallest one (Fredricks–Nelsen 2002);
  `B_δ = W` for the diagonal of `W`. A general lemma
  (`symmetric_twoIncreasing`) reduces 2-increasingness of a symmetric function
  to rectangles above the diagonal and diagonal squares.
- `Diagonal.Extremal`: `C(u,v) + C(v,u) ≤ δ(u) + δ(v)`; `K_δ` is the largest
  exchangeable copula with diagonal `δ` (Fredricks–Nelsen 1997), so every
  exchangeable `C` with diagonal `δ` satisfies `B_δ ≤ C ≤ K_δ`. If `δ ≠ id`
  then `B_δ ≠ K_δ`; hence a diagonal determines its copula if and only if it
  is the identity (`diagonal_determines_copula_iff`). In particular the
  diagonal of `W` does not determine `W`.
- `Diagonal.UpperBound`: every copula and every quasi-copula with diagonal `δ`
  lies below `A_δ(u,v) = min(u, v, max(u,v) − max_{t ∈ [u∧v, u∨v]} δ̂(t))`
  (Nelsen, Quesada-Molina, Rodríguez-Lallena and Úbeda-Flores 2004). `A_δ` is
  itself a quasi-copula with diagonal `δ`, hence the largest quasi-copula with
  that diagonal (`diagonalUpperBound_isGreatest`). For copulas it is not best
  possible in general: copulas also satisfy `C(u,v) ≤ δ(u) + δ(v) − B_δ(u,v)`,
  and for the explicit diagonal `dipDiagonal` every copula has
  `C(3/10, 7/10) ≤ 1/5 < 3/10 = A_δ(3/10, 7/10)` (`dipDiagonal_gap`). The
  best-possible upper bound for copulas with an arbitrary diagonal is not
  formalized.

`C.transpose` abbreviates coordinate exchange, and `C.survivalCopula` reflects
all coordinates. The existing `C.reflect {0}` and `C.reflect {1}` give the two
single-coordinate reflections. Their CDF formulas apply to singular copulas
as well as copulas with densities: null coordinate boundaries follow from
uniform marginals.

Exchangeable and radially symmetric copulas are closed under convex mixtures.
Equal mixtures with the transpose or survival copula provide two explicit
symmetrization constructions. Benchmarks and FGM satisfy both symmetries;
radial symmetry is also proved for the Fréchet mixture family.

## Rank symmetries

| Operation | rho | tau | footrule | gamma | beta |
| --- | --- | --- | --- | --- | --- |
| Transpose | Unchanged | Unchanged | Unchanged | Unchanged | Unchanged |
| Both coordinates reflected | Unchanged | Unchanged | Unchanged | Unchanged | Unchanged |
| One coordinate reflected | Negated | Negated | No sign rule asserted | Negated | Negated |

The footrule normalization remains the package's `[-1/2,1]` convention.
Chatterjee's xi is directional and is not covered by this table.

## Concordance and mixtures

`concordanceQ C D` is proved to equal concordance probability minus
discordance probability for independent observations with laws `C` and `D`.
The events use strict signs of `(X₀−Y₀)(X₁−Y₁)`. Ties across independent
observations have probability zero by the uniform marginals, so singular
copulas are included. Setting `D=C` gives Kendall's tau.

Q is symmetric and affine in each argument, while tau has the exact quadratic
mixture formula. Pairing Q with Π, M and W relates it to rho, footrule and
gamma. The resulting Fréchet and Mardia formulas complete the package's six
coefficient expressions for both families. See the
[rank API](rank-coefficients.md) for formulas and theorem names.

## Tail dependence

`HasLowerTailDependence C l` and `HasUpperTailDependence C l` assert both
existence and value of the relevant limit. No coefficient is assigned when
the limit has not been proved to exist.

Both definitions use a positive tail width tending to zero. The upper tail
uses the threshold `1-t`; `hasUpperTailDependence_iff_tendsto_one` proves its
equivalence with the conventional threshold tending to one. The ratios are
defined at zero using Lean's total division, but the limiting filter excludes
that point.

The API proves uniqueness, values in `[0,1]`, invariance under transposition,
exchange of upper and lower tails under full reflection, equality of tails
for radially symmetric copulas when limits exist, monotonicity in concordance
order, and affine behavior under two-component mixtures.

| Copula | Lower tail | Upper tail |
| --- | --- | --- |
| Independence | 0 | 0 |
| Comonotonicity | 1 | 1 |
| Countermonotonicity | 0 | 0 |
| FGM, all admissible parameters | 0 | 0 |
| Fréchet mixture with weight `a` on `M` | `a` | `a` |
| Mardia parameter `θ` | `θ²(1+θ)/2` | `θ²(1+θ)/2` |
| Gumbel–Hougaard, finite `θ ≥ 1` | 0 | `2−2^(1/θ)` |
| Marshall–Olkin | 1 if `α=β=1`, otherwise 0 | `min(α,β)` |
| Cuadras–Augé | 1 if `α=1`, otherwise 0 | `α` |
| Tawn, finite `θ ≥ 1` | 0 | `α+β−(α^θ+β^θ)^(1/θ)` |
| Frank, `θ > 0` | 0 | 0 |
| Gumbel–Barnett (Nelsen 4.2.9) | 0 | 0 |
| Nelsen 4.2.19 and 4.2.20, `θ > 0` | 1 | 0 |

`TailDependence.Derivative` proves the endpoint derivative rules: the right
derivative of the diagonal at zero gives the lower tail, and two minus its
left derivative at one gives the upper tail. The hypotheses are derivatives
within `[0,1]` of a real function agreeing with the diagonal on that interval.

`Diagonal.Power` covers every copula with diagonal `t^κ`: it proves `1≤κ≤2`,
upper tail `2−κ`, lower tail zero for `κ>1`, and `κ=1` exactly for `M`.
`ExtremeValue.Diagonal` derives this power form from max-stability and defines
the extremal coefficient `κ`. Thus every bivariate extreme-value copula has
both tail limits; only `M` has nonzero lower-tail dependence. Its extremal
coefficient decreases under concordance order. These proofs require neither
a density nor a Pickands representation. See also
[Gudendorf and Segers, §4](https://arxiv.org/abs/0911.1015).

The [ordinal-sum API](ordinal-sums.md) constructs binary bivariate sums with
both endpoint cases. It proves component recovery and exact lower orthant
comparison at a fixed interior split, exchangeability, PQD closure and
inheritance of lower and upper tail limits from their respective end blocks.
The converse decomposition theorem from an interior diagonal fixed point
is formalized in `Copula.OrdinalSum.Decomposition`. Ordinal sums over
arbitrary families of disjoint open intervals with a residual comonotonic
part, and their characterization by diagonal fixed points, are in
`Copula.OrdinalSum.General`, `GeneralProperties` and `GeneralDecomposition`.
Shuffle density (Theorem 3.2.2) is `Copula.Shuffle.Density`.

Further book topics include cubic sections
and tail coefficients for the remaining analytic and elliptical families.
Those results are not asserted here.

Finite signed shuffles now have a proved constructor in `Copula.Shuffle`.
Finite and increasing countable ordinal sums extend the binary constructor;
see [grid construction coverage](approximations.md) for the precise scope.
