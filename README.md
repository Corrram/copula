# copula

[![Lean](https://github.com/Corrram/copula/actions/workflows/lean.yml/badge.svg)](https://github.com/Corrram/copula/actions/workflows/lean.yml)

Finite-dimensional copulas in Lean 4, built on mathlib. This is an independent,
early-stage project intended for research use and eventual upstream contributions.
The API is still open to feedback.

## Read the mathematics

The [Copula documentation site](https://Corrram.github.io/copula/) combines
a typeset mathematical handbook with searchable, generated Lean API pages.
Featured results link to their exact formal statements and proofs. Start
with [the handbook](https://Corrram.github.io/copula/handbook/foundations/)
or [browse the API](https://Corrram.github.io/copula/api/Copula.html).
See [the documentation guide](docs/documentation.md) for local builds and
the publication workflow.

## Design

A `ProbabilityTheory.Copula d` is a probability measure on
`Fin d → unitInterval` with uniform coordinate marginals. Its distribution
function is derived as the real-valued probability of a lower orthant:

```lean
import Copula

open ProbabilityTheory
open scoped unitInterval

example (C : Copula 2) : C.cdf (fun _ => 1) = 1 := C.cdf_one

example (C : Copula 2) (u : Fin 2 → I) : 0 ≤ C.cdf u := C.cdf_nonneg u

example (C : Copula 2) (u : I) :
    C.cdf (Function.update (fun _ => 1) 0 u) = (u : ℝ) := by simp
```

This representation uses mathlib's probability measures, uniform volume on the
unit interval, products, and pushforwards. Dimension zero is supported: its CDF
is one, and groundedness is only asserted when a coordinate exists.

## What is implemented

| Module | Contents |
| --- | --- |
| `Copula.Basic` | Definition, measure accessor, extensionality, uniform marginals, construction from a random vector |
| `Copula.CDF` | Real-valued CDF, bounds, monotonicity, groundedness, boundary and marginal identities |
| `Copula.CDF.Bounds` | Fréchet–Hoeffding lower and upper bounds, including dimension zero |
| `Copula.CDF.Continuity` | The sum-distance Lipschitz estimate, continuity, and uniform continuity |
| `Copula.CDF.Extensionality` | Equality of copulas from equality of their CDFs |
| `Copula.Independence` | Product copula and the product formula for its CDF |
| `Copula.Comonotonic` | Diagonal copula and the minimum-coordinate formula for its CDF |
| `Copula.Transform` | Coordinate selection, repetition, and permutation, with composition and inverse laws |
| `Copula.Reflection` | Selected-coordinate reflections, involution, and injectivity |
| `Copula.Countermonotonic` | The bivariate reflected diagonal law and its lower-bound CDF |
| `Copula.Unique` | Uniqueness of copulas in dimensions zero and one |
| `Copula.Rectangle` | Alternating CDF sums, rectangle probabilities, and the increasing property |
| `Copula.Classical` | Equivalence of the classical conditions and measure-based copulas in every finite dimension; `ofClassical` constructor |
| `Copula.Classical.Regularity` | Rectangle splitting, monotonicity, and Lipschitz continuity derived from the classical conditions |
| `Copula.Classical.Approximation` | Finite atomic approximations with CDF error at most `d / 2^n` |
| `Copula.Distribution.ProbabilityIntegralTransform` | Uniformity of continuous CDF transforms and continuity for atomless laws |
| `Copula.Distribution.Quantile` | Quantile adjunction and inverse-transform sampling, including atoms |
| `Copula.Distribution.RandomizedInverse` | Randomized inverses obtained by disintegration |
| `Copula.Distribution.GammaLaplace` | Exponential tilting and the rate-one gamma Laplace transform |
| `Copula.Sklar` | General Sklar existence, uniqueness on marginal ranges, and full uniqueness for continuous marginals |
| `Copula.Families.Gaussian` | Gaussian copulas from positive semidefinite correlation matrices, including singular matrices |
| `Copula.Families.Gaussian.Identities` | Identity correlation gives independence; all-ones correlation gives comonotonicity; coordinate selection corresponds to submatrices |
| `Copula.Families.Clayton` | Positive-parameter gamma-frailty construction with atomless marginals and Sklar factorization |
| `Copula.Families.Clayton.CDF` | Joint frailty tails, explicit marginal CDFs, and the classical Clayton CDF formula |
| `Copula.Families.Clayton.Limits` | Pointwise CDF convergence to independence at zero and comonotonicity at infinity |
| `Copula.Archimedean.Basic` | Bivariate generator admissibility from convexity, measure construction, and Archimedean classification |
| `Copula.Archimedean.Power`, `Truncated`, `Symmetry` | Outer and inner generator powers, non-strict generators, and Archimedean exchangeability |
| `Copula.Archimedean.Clayton` | Identification of the Clayton generator in every dimension; BB1 construction and CDF |
| `Copula.Families.Gumbel`, `Joe`, `Frank` | Proved bivariate generators and CDFs; Gumbel and Tawn max-stability; BB6 |
| `Copula.ExtremeValue.Basic` | Max-stability, independence and comonotonicity, closure under power products |
| `Copula.Transform.MaxProduct` | Independent maxima with coordinatewise power weights, including zero weights; exact CDF |
| `Copula.Families.MarshallOlkin` | Marshall–Olkin, Cuadras–Augé and finite-dimensional common-shock copulas |
| `Copula.Elliptical.ScaleMixture` | Positive Gaussian scale mixtures with atomless marginals and Sklar factorization |
| `Copula.Families.StudentT`, `ScaleMixtures` | Student-t, Cauchy, variance-gamma, Laplace, slash and normal–lognormal copulas |
| `Copula.Topology.Uniform`, `Topology.Closed` | Equicontinuity of copula CDFs, pointwise-implies-uniform convergence, closedness and compactness of the copula set (Nelsen §2.10) |
| `Copula.Diagonal.Construction` | Every diagonal function is the diagonal of a copula (Nelsen §3.2.6) |
| `Copula.Diagonal.Bertino`, `Extremal`, `UpperBound` | Prescribed diagonals (Nelsen §3.2.6): Bertino copula `B_δ`, the smallest copula with diagonal `δ` (Fredricks–Nelsen 2002); `K_δ` is the largest exchangeable one (Fredricks–Nelsen 1997); `A_δ` is the largest quasi-copula with diagonal `δ` (Nelsen et al. 2004) but not best possible for copulas (explicit example); `δ` determines its copula iff `δ = id` |
| `Copula.Families.QuadraticSections` | Copulas with quadratic sections `uv + ψ(v)u(1−u)` (Nelsen §3.2.5): copula iff `ψ(0) = ψ(1) = 0` and `ψ` 1-Lipschitz; quadratic sections in both variables iff FGM |
| `Copula.Archimedean.Theory`, `TheoryConvex`, `Diagonal` | Strict Archimedean copulas lie below `M`; generator diagonals `δ(t) = ψ(2φ(t)) < t` |
| `Copula.Families.NelsenTable.N9`, `N10`, `N13`, `N19`, `N20` | Gumbel–Barnett and Nelsen families #10, #13, #19, #20: generators, CDFs and boundary formulas |
| `Copula.Archimedean.Clamp`, `Copula.Families.NelsenTable.N11`, `N16`, `N17`, `N18`, `N21`, `N22`, `Limits`; `Copula.TailDependence.NelsenTable` | Non-strict generators by clamping; Nelsen families #11, #16, #17, #18, #21, #22 on their full ranges (with #13 now for all θ > 0): generators, CDFs (corrected #22 formula), special cases `C_0 = W` (#16), `C_{-1} = Π` (#17), `C_1 = W` (#21), limits `C_∞ = Π/(Σ−Π)` (#16) and `C_∞ = M` (#18), `λ_L = 0` for the non-strict families |
| `Copula.Measures.Deviation`, `SchweizerWolff`, `Hoeffding` | Integrals of `φ(C − Π)`; Schweizer–Wolff's σ and Hoeffding's Φ² with invariances, zero characterizations and FGM values |
| `Copula.RandomVariable.Invariance`, `Independence`, `Monotone`, `Symmetry`, `Ext` | Sklar copulas under strictly monotone transformations, independence, functional dependence (`M`/`W`) and symmetry of random vectors |
| `Copula.QuasiCopula.Basic`, `Bivariate`, `PrescribedValue`, `PrescribedValueBest`; `Copula.Distribution.RealQuantile` | Quasi-copulas (Nelsen §6.2): Fréchet bounds, closure under sup/inf/mixtures, boundary-rectangle characterization (Genest et al.), a proper quasi-copula; best-possible bounds for a prescribed value `C(a,b) = θ` (Nelsen Thm 3.2.3); real quantiles used for the converse of Nelsen Thm 2.5.4 in `RandomVariable.Monotone` |
| `Copula.Mixture` | Finite convex mixtures of copulas and their CDF formulas |
| `Copula.Vine` | C-, D-, and regular vines with measurable conditional pair families, including non-simplified and singular inputs; proved proximity, conditional gluing and marginal preservation; direct simplified C-vine CDFs |
| `Copula.OrdinalSum` | Binary, finite and increasing countable ordinal sums; binary converse decomposition, probability laws, rank formulas, ordering, PQD and tails |
| `Copula.Checkerboard` | Rectangular nonuniform checkerboard, check-min and check-W constructions; exact cell recovery, grid interpolation and uniform error bounds |
| `Copula.Shuffle` | Finite shuffles of min with unequal strip widths and per-segment reflections |
| `Copula.Shuffle.Weights`, `Shuffle.Density` | Straight shuffles of `M` from weight vectors with zero entries (`weightShuffle`, a genuine `shuffleOfMin`); grid shuffles agreeing with `C` on the grid, uniform error `≤ 2/n`, density of (straight) shuffles of `M` in the uniform metric (Nelsen Thm 3.2.2, Mikusiński–Sherwood–Taylor) |
| `Copula.OrdinalSum.General`, `GeneralProperties`, `GeneralDecomposition` | General ordinal sums over any family of disjoint open intervals, `M` on the gaps (Nelsen Def 3.2.1): CDF formulas, component recovery and uniqueness, diagonal fixed points, transpose, order, PQD; finite, countable and binary sums as instances; characterization by diagonal fixed points (Nelsen Thm 3.2.1) |
| `Copula.Bernstein` | Positive-degree tensor Bernstein copulas, copula validity, benchmark identities, quantitative error bounds and uniform convergence |
| `Copula.Families.FGM`, `Frechet` | FGM on the full parameter interval, Fréchet mixtures and Mardia endpoint identities |
| `Copula.Families.Nelsen`, `Nelsen7`, `Clayton.Negative` | Nelsen 2, 7, 12, 14, Genest–Ghoudi and negative bivariate Clayton; CDFs and endpoint identities |
| `Copula.Dependence.NelsenEndpoints` | Nelsen 12 and 14 have TP2 CDFs, are PQD, and are non-CD for all θ≥1; CI and MTP2 density are checked at θ=1 |
| `Copula.Dependence.GumbelTotalPositivity`, `MaxProductTotalPositivity` | CDF TP2 for Gumbel, Tawn, Marshall–Olkin and Cuadras–Augé across all admissible parameters; max-product preservation |
| `Copula.Dependence.BB1TotalPositivity` | A positive log-convex inverse generator yields a TP2 CDF; BB1 satisfies this for its full positive parameter range |
| `Copula.Dependence.ConditionalMonotonicity` | Two-direction CI/CD, directional SD, reflection duality, benchmarks and FGM classification |
| `Copula.Rank.FGMKendall`, `FGMChatterjee`, `Frechet` | FGM conditional CDF, Kendall tau and Chatterjee xi; Fréchet/Mardia Spearman rho |
| `Copula.Rank.Concordance`, `ConcordanceProbability`, `KendallMixture` | Concordance probabilities, the cross function Q, and finite-mixture tau formulas |
| `Copula.Rank.FrechetKendall`, `FrechetChatterjee` | Complete six-coefficient formulas for Fréchet and Mardia, including singular endpoints |
| `Copula.Order.Frechet` | Increasing upper-bound weight and decreasing lower-bound weight increase the copula |
| `Copula.Order.FGMSchur`, `SymmetricSchur` | Exact FGM Schur order by absolute parameter; two-direction comparison |
| `Copula.Rank` | Six population dependence coefficients, sharp ranges and benchmark values; Spearman CDF and distance formulas; mixture identities and FGM formulas |
| `Copula.Dependence` | PQD, LTD, RTI, SI and total positivity of CDFs, conditional kernels and densities; implication and mixture theorems, rank consequences and FGM classifications |
| `Copula.Order` | Lower/upper orthant, concordance, supermodular and directional Schur comparisons; rank monotonicity, extremal copulas and FGM parameter ordering |
| `Copula.Diagonal` | Diagonal regularity, characterization of comonotonicity, and distributions of coordinate extrema |
| `Copula.Reflection.Bivariate`, `Copula.Symmetry` | Reflection/survival CDF formulas, exchangeability, radial symmetry and symmetrization |
| `Copula.Rank.Symmetry` | Transpose and survival invariance of five coefficients; single-reflection sign identities |
| `Copula.TailDependence` | Explicit tail-limit predicates, bounds, uniqueness, order/mixture results and six benchmark/family formulas |
| `Copula.Measures.CDFDistance`, `CDFDistanceSymmetry`, `CDFDistanceMixture`, `CDFDistanceBenchmarks`, `HoeffdingBounds` | Hoeffding's D, Blum–Kiefer–Rosenblatt R, Bergsma–Dassios τ*, distance correlation; symmetries, dilution by independence, `Φ²(M) = Φ²(W) = 1`, `0 ≤ 30 D ≤ 1` |
| `Copula.Measures.Uniform`, `Copula.Topology.UniformDistance` | Uniform CDF distance of copulas; Schweizer–Wolff's κ = 4 sup \|C − Π\| with attainment, `\|β\| ≤ κ ≤ 1`, `σ ≤ 3κ`, invariances |
| `Copula.Measures.Bounds` | Sharp bounds `σ ≤ 1`, `Φ² ≤ 1` with equality iff `C ∈ {M, W}`, and `κ = 1 ↔ \|β\| = 1` (Nelsen §5.3.1), via the SI rearrangement |
| `Copula.Rearrangement`, `Rearrangement.Decreasing`, `Primitive`, `LevelSet`, `PrimitiveIntegral`, `SI` | Graph copulas, complete dependence and generalized shuffles; decreasing rearrangements, primitive comparison lemma, SI rearrangement of Strothmann–Dette–Siburg |
| `Copula.MarkovProduct`, `MarkovProduct.Laws` | Darsow–Nguyen–Olsen Markov product: associativity, `M`/`Π`/`W` laws, `(A * B)ᵀ = Bᵀ * Aᵀ`, CDF formula, `Cᵀ * C = M ↔ ξ(C) = 1`, `ξ(A * B) ≤ ξ(B)` |
| `Copula.Transform.Gluing` | Siburg–Stoimenov gluing of copulas along an interval partition; strip formula and section derivatives |
| `Copula.Rank.Blest`, `BlestBounds`, `CorrelationRatio`, `Sobolev`, `MixtureMeasure`; `Copula.Information`, `Copula.KendallDistribution` | Blest's ν and its symmetrization, copula correlation ratio, Sobolev dependence, mixtures; copula information (KL divergence to Π); Kendall distribution function |
| `Copula.Families.ProductPerturbation` | Copulas `uv + φ(u) ψ(v)` for Lipschitz boundary profiles |
| `Copula.Archimedean.Associativity`, `LevelCurves` | Commutativity, associativity and generator scaling `cφ` (Nelsen Thm 4.1.5); level curves and zero set, convexity of the generator and of level curves (Thm 4.3.2), strictness iff positivity on `(0,1]²` |
| `Copula.Archimedean.TailDependence`, `TailFamilies` | Tail coefficients via generators (Nelsen Cor 5.4.3), `δ'(1⁻)`, `λ_L = 0` for non-strict and `λ_U = 0` for `ψ'(0) ≠ 0`; Frank and Gumbel–Barnett (0, 0), families #19 and #20 (`λ_L = 1`, `λ_U = 0`) |
| `Copula.Archimedean.Derivative`, `KendallDistribution`, `KendallCDF`, `KendallTau`, `KendallTauFamilies`, `KendallTauAMH`, `KendallTauFrank` | C¹ generators (strict or not): conditional CDFs as partial derivatives; Kendall distribution `K_C(t) = t − φ(t)/φ'(t)` (Nelsen Thm 4.3.4) and zero-set mass `−φ(0)/φ'(0⁺)` (Thm 4.3.3); `τ = 1 + 4∫₀¹ φ/φ'` (Cor 5.1.4) and `τ_{φ^δ} = 1 + (τ_φ − 1)/δ`; τ of Clayton, Gumbel, Ali–Mikhail–Haq, BB1, Nelsen #2, #12 and #14; Frank's τ as an elementary integral |
| `Copula.Rank.Region.Common` | Shared support of the ξ–ρ, ξ–Blest, ξ–β, τ–footrule–β and mean–variance region developments (centered ordinal sums, diagonal bands, two-strip copulas, increasing shuffles, SI bounds for ξ); the old `Region.<X>.Support.*` paths re-export it under their namespaces |
| `Copula.Archimedean.Uniqueness`, `Converse` | Generator uniqueness up to a positive factor: `C_{φ₁} = C_{φ₂}` iff `φ₂ = cφ₁` (Genest–MacKay; Nelsen §4.1); the "only if" of Nelsen Thm 4.1.4 (an Archimedean formula that is a copula has a convex generator), via antitone functions with nondecreasing increments |
| `Copula.Archimedean.KendallTauGenerator`, `KendallTauFrankDebye`, `KendallTauTable`, `KendallTauIntegral` | Cor 5.1.4 from a differentiable generator `φ`; Frank's τ in Debye form `1 − (4/θ)(1 − D₁(θ))` for `θ > 0` and `θ < 0`; closed-form τ of negative Clayton and families #7, #8, #15, #16, #18; τ of Joe and families #9, #13, #19, #20 as explicit integrals |
| `Copula.Archimedean.KendallTauRemaining`, `KendallTauRemaining2` | Kendall's τ of Nelsen families #10, #11, #17, #21, #22 as explicit integrals `1 + 4∫₀¹ φ/φ'` (no elementary closed form); checked numerically against simulation |
| `Copula.Archimedean.Concordance`, `ConcordanceFamilies` | Nelsen Thm 4.4.2 (`C₁ ≤ C₂` iff `φ₁ ∘ ψ₂` subadditive, strict `ψ₂`) and Cor 4.4.3 (concave); PQD iff `ψ(x)ψ(y) ≤ ψ(x+y)`, non-strict never PQD, NQD iff `φ(uv) ≤ φ(u)+φ(v)`; Clayton increasing in `θ`; families #9, #10 NQD, #13 PQD (`θ ≥ 1`) / NQD (`θ ≤ 1`), #19, #20 PQD |
| `Copula.Archimedean.QuadrantCriteria`, `QuadrantLogConvex`, `QuadrantFrank`, `QuadrantJoe`, `QuadrantTails`, `QuadrantNelsenB`, `QuadrantNelsenC`, `QuadrantN16`, `QuadrantN17`, `QuadrantClassification` | Complete PQD/NQD classification of Nelsen Table 4.1 (#1-#22, all parameter ranges) plus Gumbel, Frank (both signs), Joe, AMH: generator criteria `isPQD_iff_psi`, `isNQD_iff_psi`, `isPQD_of_phi`, strict log-convexity of `ψ` (Frank, Joe, #17), tail-coefficient obstructions, explicit witnesses; one theorem `*_quadrant` per family |
| `Copula.TailDependence.NelsenTableUpper`, `NelsenTableLower`; `Copula.Families.NelsenTable.LimitsZero`, `LimitsInfinity` | `λ_U = 0` for families #7, #10, #11, #13, #16, #17, #22; `λ_L = 0` for #10, #13, #17; `λ_U = 2 − 2^{1/θ}` for #21; limits `C₀ = Π` (#11, #22), `C_∞ = M` (#17, #21), and `C_{−∞} = max(0, (uv+u+v−1)/2)` (#17, the member `θ = 1/2` of #7, not `W`) |
| `Copula.Archimedean.BlomqvistTable`, `BlomqvistTableN`, `SpearmanRhoGenerator` | Blomqvist's β `= 4C(½,½) − 1` in closed form for Nelsen Table 4.1 families #1 (both signs), #2, #3, #5 (both signs), #6, #7, #8, #9-#22 (#4 in `Rank.PowerDiagonal`); generic `β = 4ψ(2φ(½)) − 1` and `ρ = 12∬ψ(φ(u)+φ(v)) − 3` for any bivariate generator |
| `Copula.Archimedean.SpearmanRhoAMH`, `SpearmanRhoNelsen9`, `SpearmanRhoNelsen2` | Spearman's ρ: AMH as the series `12 Σ θᵏ/((k+1)²(k+2)²) − 3` (`\|θ\| ≤ 1`); Gumbel–Barnett (#9) as the one-dimensional integral `12∫₀¹ v/(2 − θ log v) dv − 3`; Nelsen #2 in closed form `4Γ(1+1/θ)²/Γ(1+2/θ) − 3` (layer cake and the volume of the `ℓ^θ` ball) |
| `Copula.Archimedean.DebyeTwo`, `SpearmanRhoFrank` (+ `SpearmanRhoFrankCalculus`, `SpearmanRhoFrankCore`), `SpearmanRhoAMHEndpoints`, `SpearmanRhoAMHDilog` | Debye function of order two `D₂(θ) = (2/θ²)∫₀^θ t²/(e^t−1)dt`; Spearman's ρ of Frank's copula `1 − (12/θ)(D₁(θ) − D₂(θ))` for `θ > 0` and `θ < 0` (Fubini over the cube `(0,θ]³`, no differentiation under the integral); AMH endpoints `ρ(1) = 4π² − 39`, `ρ(−1) = 33 − 48 log 2`; AMH `ρ` in dilogarithm form for `0 < \|θ\| < 1` |
| `Copula.Concordance.Continuity`, `Axioms` | Continuity of ρ, τ, β, γ and footrule under pointwise (= uniform) convergence; Scarsini's axioms `IsMeasureOfConcordance` (Nelsen Def 5.1.7) for ρ, τ, β, γ, with consequences (survival invariance, zero under a single-reflection symmetry, ±1 at a.s. monotone dependence, signs under PQD/NQD, convex combinations); ξ, σ, Φ² and the footrule are not measures of concordance |
| `Copula.Concordance.Daniels`, `CaperaaGenest` | Daniels' inequality `\|3τ − 2ρ\| ≤ 1` (Nelsen §5.1.3) from the exact (τ, ρ) region; Capéraà–Genest: LTD ∧ RTI (in particular SI) implies `0 ≤ τ ≤ ρ ≤ 3τ` |
| `Copula.Dependence.HierarchyCorner`, `HierarchyDensity`, `HierarchyExamples` | LCSD/RCSI (Nelsen §5.2.3) and their equivalence with TP2 of the CDF/survival function, implications to LTD/RTI in both directions; TP2 of the copula measure on ordered product sets, implied by an MTP2 density and implying SI in both directions, LCSD and RCSI; `M` is TP2 as a measure without a density; product-perturbation counterexamples: PQD ⇏ LTD, RTI ⇏ LTD, LTD ⇏ RTI, LTD ∧ RTI ⇏ SI, SI(V\|U) ⇏ SI(U\|V) |
| `Copula.Multivariate.LowerBound`, `LowerBoundAttained` | The lower Fréchet–Hoeffding bound `W_d`: a quasi-copula, `W_2 = W`, the `W_d`-volume of `[1/2,1]^d` is `1 − d/2`, so `W_d` is not a copula for `d ≥ 3`; Nelsen §2.10: for every `u` some `d`-copula (a cyclic shift of a uniform variable) attains `W_d(u)`, hence `W_d = inf_C C` pointwise and there is no smallest `d`-copula for `d ≥ 3` |
| `Copula.Multivariate.Margins`, `Survival` | CDFs of margins and reindexed copulas (`cdf_reindex`, other arguments set to `1`), margins of `Π_d`, `M_d` and of reflections/survival copulas; `C = Π_d` iff the coordinates are independent iff `C = ∏ uᵢ`; `d`-dimensional survival function as the `C`-volume of `[u,1]` (inclusion–exclusion), survival copula `Ĉ(u) = C̄(1−u)`, CDF of any partial reflection, radial symmetry of `Π_d` and `M_d` |
| `Copula.Archimedean.MultivariateMonotone`, `Multivariate`, `MultivariateClayton` | `d`-monotone functions (McNeil–Nešlehová Def 2.3) and nonnegativity of their alternating corner sums; `ψ(φ(u₁)+⋯+φ(u_d))` is a `d`-copula for continuous `d`-monotone `ψ` (McNeil–Nešlehová Thm 2.2, Kimberling), with margins of the same generator and the bivariate construction for `d = 2`; Clayton in every dimension (`θ > 0`, equal to the gamma-frailty construction; `−1/(d−1) ≤ θ < 0`), and the Clayton formula with `θ < 0` is a `d`-copula iff `θ ≥ −1/(d−1)` |
| `Copula.Multivariate.Concordance` | Multivariate Kendall's τ and Spearman's ρ (Joe 1990; Nelsen 1996; Schmid–Schmidt 2007): reduction to τ, ρ for `d = 2`, `∫ C dΠ = ∫ ∏(1−xᵢ) dC`, values `0` at `Π_d` and `1` at `M_d`, `τ_d ≤ 1`, `τ_d ≥ −1/(2^{d−1}−1)`, `ρ_d ≤ 1` and monotonicity of `ρ_d` |
| `Copula.Elliptical.GaussianOrthant`, `Copula.Families.Gaussian.Bivariate` | Sheppard's orthant formula `P(X ≤ 0, Y ≤ 0) = 1/4 + arcsin r/(2π)` for centered bivariate normal laws (polar coordinates, Cramér–Wold on `ℝ²`); the explicit bivariate normal law `bivariateNormal r` and its linear forms; the bivariate Gaussian copula `bivariateGaussian r` as the law of `(Φ(X), Φ(Y))`, `C_r(Φ(x), Φ(y)) = P(X ≤ x, Y ≤ y)`; `r = 0, 1, −1` give `Π`, `M`, `W`; exchangeability, radial symmetry, and `r ↦ −r` under a single reflection |
| `Copula.Families.Gaussian.Sheppard`, `Slepian`, `Tail` | Gaussian copula: `β = τ = (2/π) arcsin r`, `ρ_S = (6/π) arcsin(r/2)` (strictly increasing in `r`); Slepian's inequality `r ≤ r' → C_r ≤ C_{r'}` (common-factor representation and Chebyshev's integral inequality); PQD iff `r ≥ 0`, NQD iff `r ≤ 0`; conditional CDF representation; tail independence `λ_L = λ_U = 0` iff `r < 1` |
| `Copula.Elliptical.ScaleMixtureConcordance`, `ScaleMixtureSymmetry` | Bivariate Gaussian scale mixtures (Student-t for every `ν > 0`, Cauchy, variance-gamma, Laplace, slash, normal–lognormal): `τ = (2/π) arcsin r` (Lindskog–McNeil–Schmock) and `β = (2/π) arcsin r` for every mixing law; exchangeability and radial symmetry |
| `Copula.ExtremeValue.Pickands`, `PickandsConverse`, `PickandsCoefficients`, `PickandsSpearman`, `PickandsKendall`, `PickandsFamilies`, `PickandsGalambos`, `PickandsHueslerReiss` | Bivariate Pickands representation: for convex `A` with `max(t,1−t) ≤ A ≤ 1`, `C_A(u,v) = exp(log(uv) A(log v/log(uv)))` is a max-stable copula (2-increasingness from submodularity of `ℓ_A(x,y) = (x+y)A(y/(x+y))`); conversely every bivariate extreme-value copula is `C_A` with `A(t) = −log C(e^{−(1−t)}, e^{−t})` (convexity via an argmax argument, no spectral measure); `A ↦ C_A` injective and order-reversing, `A ≡ 1` gives `Π`, `A = max(t,1−t)` gives `M`; every EV copula is PQD; `λ_U = 2(1 − A(1/2))`, `λ_L = 0` unless `M`, `β = 2^{2(1−A(1/2))} − 1`, footrule `6/(2A(1/2)+1) − 2`, Spearman `ρ = 12∫₀¹ (A(t)+1)⁻² dt − 3`; Kendall `τ = 1 − ∫₀¹ (A − tA')(A + (1−t)A')/A² dt` (differentiable `A`) and `τ = ∫₀¹ t(1−t)A''(t)/A(t) dt` (twice differentiable `A`); Gumbel, Marshall–Olkin, Cuadras–Augé and Tawn identified with their Pickands functions; Galambos copula (`θ > 0`, convexity via reverse Minkowski) with its classical CDF and `λ_U = 2^{−1/θ}`; Hüsler–Reiss copula (`λ > 0`, `A' = Φ(λ + z/(2λ)) − Φ(λ − z/(2λ))` nondecreasing), exchangeable, `λ_U = 2(1 − Φ(λ))` |
| `Copula.ExtremeValue.Archimax` | Archimax copulas (Capéraà–Fougères–Genest 2000) `C(u,v) = ψ(ℓ_A(φ(u), φ(v))) = ψ((φ(u)+φ(v)) A(φ(v)/(φ(u)+φ(v))))` for a bivariate Archimedean generator and a Pickands function: a copula (`ψ` convex nonincreasing, `ℓ_A` nondecreasing and submodular); `A ≡ 1` gives the Archimedean copula, `ψ = e^{−t}` the extreme-value copula `C_A`, `A = max(t,1−t)` gives `M`; order-reversing in `A` and above the Archimedean copula; transpose; diagonal `ψ(2A(1/2)φ(t))`, Blomqvist's β; `λ_U = 2(1 − A(1/2))` when `ψ'(0+)` is finite and nonzero (general limit form), `λ_L = lim ψ(2A(1/2)x)/ψ(x)` for strict generators |
| `Copula.Multivariate.SpearmanLowerBound` | `∫ W_d dΠ_d = 1/(d+1)!` (volume of a simplex, by induction on `d`), hence `∫ C dΠ ≥ 1/(d+1)!` and the lower bound `ρ_d ≥ (2^d − (d+1)!)/(d!(2^d − d − 1))` of multivariate Spearman's rho (`ρ₃ ≥ −2/3`) |
| `Copula.Families.Plackett` (`Basic`, `Order`, `Spearman`, `Tail`) | Plackett family (Nelsen §3.3.1) for all `θ > 0`: copula via a derivative criterion for 2-increasingness (positive discriminant, positive density `θ(1+(θ−1)(u+v−2uv))/disc^{3/2}`), `C_1 = Π`, constant cross-product ratio `C(1−u−v+C) = θ(u−C)(v−C)`, exchangeability, radial symmetry, `β = (√θ−1)/(√θ+1)`; positively ordered in `θ` (PQD for `θ ≥ 1`, NQD for `θ ≤ 1`), `M − C_θ ≤ 1/√θ` and `C_θ − W ≤ √θ` (limits `M` at `∞`, `W` at `0⁺`); Spearman `ρ = (θ+1)/(θ−1) − 2θ log θ/(θ−1)²`; tail independence `λ_L = λ_U = 0` |
| `Copula.Families.Plackett.Kendall`, `KendallOrder`, `KendallArctan` | Plackett Kendall's tau (no elementary closed form): `τ = 1 − 4∬ ∂_uC ∂_vC` with the explicit partial derivatives, the rational form `τ = (θ+1)/(θ−1) − 2θ/(θ−1)∬ (1+(θ−1)(u+v−2uv))/disc`, and the one-dimensional form `τ = (θ+1)/(θ−1) − 2θρ/(θ−1)² + 4(θ+1)√θ/(θ−1)² ∫₀¹ √(v(1−v)) arctan((1−(θ+1)v)/(2√θ√(v(1−v)))) dv`; full support of `C_θ`, injectivity in `θ`, `τ` and `ρ` strictly increasing, `τ, ρ > 0 ⇔ θ > 1`, `< 0 ⇔ θ < 1`, values in `(−1,1)`, limits `±1` as `θ → ∞`, `0⁺` |
| `Copula.Order.StrictKendall` | `τ(D) − τ(C) = 4(∫(D−C)dD + ∫(D−C)dC)`; strict monotonicity of Kendall's tau under the concordance order when one of the copulas has full support (`IsOpenPosMeasure`) |
| `Copula.Archimedean.MultivariateConverse` | McNeil–Nešlehová (2009) Theorem 2.2, "only if": the inverse generator of a `d`-dimensional Archimedean copula is `d`-monotone (`HasArchimedeanGenerator.isMultiplyMonotone`), so `ψ(Σφ(uᵢ))` is a `d`-copula iff `ψ` is `d`-monotone (`exists_hasArchimedeanGenerator_iff`); Williamson's characterization `IsMultiplyMonotone n f ↔` nonnegative alternating corner sums of orders `≤ n` (differentiability derived from convexity of the difference quotients); inverse generators are continuous on `[0, ∞)` |
| `Copula.Families.Khoudraji`, `Raftery`, `RafterySpearman` | Khoudraji's asymmetrization `u^{1−a}v^{1−b}C(u^a,v^b)` as Liebscher's product with `Π`: endpoint weights, `K(Π) = Π`, Marshall–Olkin `= K(M)`, Tawn `= K(Gumbel)`, preservation of max-stability, order, PQD/NQD, transposition law, `K_{a,b}(M)` exchangeable iff `a = b` or `ab = 0`; Raftery family (`0 ≤ θ < 1`) via the derivative criterion (no singular component), Nelsen's closed form, `C_0 = Π`, `\|M − C_θ\| ≤ (1−θ)/(1+θ)` (`C_θ → M`), exchangeable, PQD, diagonal, `β`, `λ_L = 2θ/(1+θ)`, `λ_U = 0`, Spearman `ρ = θ(4−3θ)/(2−θ)²` |
| `Copula.MarkovProduct.Algebra`, `Checkerboard`, `Invertible` | Markov product: bilinearity in mixtures, `(aM+(1−a)Π)(bM+(1−b)Π) = abM+(1−ab)Π`, products of `M`/`W` mixtures; idempotents (`M`, `Π`, not `W`, transposes, `aM+(1−a)Π` iff `a ∈ {0,1}`, `C*Cᵀ` for left invertible `C`); `C` has a left inverse iff `ξ(C) = 1`, a right inverse iff `ξ(Cᵀ) = 1`, two-sided inverses are unique and equal `Cᵀ`; conditional CDFs of checkerboard copulas (cell densities), the transpose of a checkerboard, and the product of checkerboards over a common middle grid is the checkerboard of the width-normalized matrix product `∑ⱼ aᵢⱼbⱼₖ/|Qⱼ|`; `ξ(C) = 1` iff `C` is completely dependent (`V = f(U)` a.s.; distribution functions with values in `{0,1}` are Dirac), hence `C` is left invertible iff completely dependent, right invertible iff `Cᵀ` is, and invertible iff mutually completely dependent (Darsow–Nguyen–Olsen); `M` is the only completely dependent idempotent |
| `Copula.Families.RafteryKendall` | Kendall's tau of the Raftery family, `τ(C_θ) = 2θ/(3−θ)`: conditional distribution functions = classical partial derivatives a.e., `τ = 1 − 4∬∂₁C∂₂C` split along the diagonal and integrated in closed form |
| `Copula.ExtremeValue.ArchimaxTail` | Tail coefficients of Archimax copulas under regular variation (Capéraà–Fougères–Genest 2000, §4): inversion of regular variation for monotone functions; `φ(1−at)/φ(1−t) → a^m` gives `λ_U = 2 − (2A(1/2))^{1/m}`; strict `φ` with `φ(at)/φ(t) → a^{−k}` gives `λ_L = (2A(1/2))^{−1/k}`; non-strict generators with `A(1/2) > 1/2` give `λ_L = 0`; Gumbel–Archimax example `λ_U = 2 − (2A(1/2))^{1/θ}` |
| `Copula.Multivariate.SpearmanLowerBoundStrict` | The lower bound `(2^d − (d+1)!)/(d!(2^d − d − 1))` of multivariate Spearman's rho is not best possible for `d ≥ 3`: `∫ C dΠ ≥ e^{−d} > 1/(d+1)!` (tangent line of `exp`, `E log(1−U) = −1`), hence `ρ_d ≥ (d+1)/(2^d−d−1)·(2^d e^{−d} − 1)` with a uniform gap; `ρ₃ ≥ 8e^{−3} − 1 ≈ −0.6017 > −2/3` |
| `Copula.Elliptical.StudentTTail` (`Polar`, `MixtureTail`, `TailDependence`), `Copula.Families.StudentT.GammaSmallBall`, `Distribution`, `Normalization` | Tail dependence of the bivariate Student-t copula (Embrechts–McNeil–Straumann 2002; Hult–Lindskog 2002): `λ_L = λ_U = ∫_{arccos(r)/2}^{π/2} cos^ν / ∫_0^{π/2} cos^ν = 2 t_{ν+1}(−√((ν+1)(1−r)/(1+r)))` for every real `ν > 0` and `r ∈ (−1, 1]`, positive for `r > −1` (unlike the Gaussian copula), `0` at `r = −1`; regularly varying Student-t orthant tails via gamma small-ball bounds and dominated convergence, Gaussian homogeneous moments in polar coordinates; the Student-t density/CDF with the `x = √n tan θ` substitution; `Normalization`: the Wallis integral `∫_{−π/2}^{π/2} cos^p = √π Γ((p+1)/2)/Γ(p/2+1)` for real `p > −1` (Gaussian moments in polar coordinates) and the classical density `Γ((n+1)/2)/(√(nπ)Γ(n/2)) (1 + x²/n)^{−(n+1)/2}` |
| `Copula.Families.StudentT.TailMonotone` | Monotonicity of the Student-t tail coefficient `λ(ν, r)` (Embrechts–McNeil–Straumann 2002, Demarta–McNeil 2005): strictly increasing in `r ∈ [−1, 1]`, strictly decreasing in `ν > 0` for `r ∈ (−1, 1)` (Chebyshev-type ratio inequality for `∫ cos^ν`), `λ → 0` as `ν → ∞` for `r < 1` (Gaussian tail independence, explicit bound `((π − 2a)/a)(cos a / cos(a/2))^ν`), `λ → 1 − arccos(r)/π` as `ν → 0⁺`, which is a strict upper bound |
| `Copula.Families.StudentT.Marginal` | Margins of the multivariate t law: `studentTMeasure ν` (density `studentTPDF ν`, CDF `studentTCDF ν`, continuous); the law of `G^{−1/2} Z` with `G ~ Gamma(ν/2, ν/2)` is `t_ν` (Tonelli + Gamma integral); every coordinate of `studentTLaw R ν` with `R i i = 1` is `t_ν`, so `studentT` is the unique copula with `C(T_ν(x₁), …, T_ν(x_d)) = P(X ≤ x)` |
| `Copula.Multivariate.SpearmanInfimumDual`, `SpearmanInfimumThree`, `SpearmanInfimumWitness` | Sharp lower bound for the infimum of multivariate Spearman's rho by a dual certificate for the convex-order minimum of sums of exponentials (Wang–Wang 2011; Bernard–Jiang–Wang 2014): `∫ C dΠ ≥ L_d(c) = d∫₀ᶜ q'(x)(log(1−(d−1)x)+dx−1)dx − q(c)log q(c) + q(c)`, `q(x) = x(1−(d−1)x)^{d−1}`, `0 < c ≤ 1/(d(d−1))`; closed form for `d = 3`, optimal `c₃` with `log((1−2c)/c) = 3−9c`, `ρ₃ ≥ 8(c₃ − 11c₃²/2 + 12c₃³ − 9c₃⁴) − 1 ≈ −0.5615741` and certified `ρ₃ ≥ −0.56158`; an explicit 3-copula (six segments, piecewise affine measure-preserving maps) with `ρ₃ = −631/1125 ≈ −0.560889`, so `inf ρ₃ ∈ [−0.56158, −631/1125]` |

Import `Copula` for the full library or a specific module such as
`Copula.Basic`. Declarations live in `ProbabilityTheory.Copula`; the structure
itself is `ProbabilityTheory.Copula`.

[Grid approximations, shuffles and Bernstein copulas](docs/approximations.md)
have constructors with proved validity, and quantitative approximation guarantees.

[Ordinal sums](docs/ordinal-sums.md) combine different copulas on ordered
intervals. The binary API proves that lower and upper tails come from
the respective component blocks, allowing asymmetric tail dependence.
Their probability laws, integration formulas, and exact rho, tau, footrule
and common-split concordance formulas are proved, with sharp bounds and
explicit independent-component and countermonotonic-component examples.
The converse is proved as well: an interior point with `C(a,a)=a` gives
explicit component copulas, uniquely determined at that split. Equivalent
probability criteria identify these cuts without assuming a density.

The CDF is 1-Lipschitz for the sum of coordinate distances. Lean's default
metric on `Fin d → unitInterval` is the maximum metric; the theorem
`Copula.lipschitzWith_cdf` uses constant `d` for that metric.

`IsClassical.existsUnique` proves the full classical characterization, including
dimension zero. `Copula.ofClassical F hF` constructs its unique representing
copula, and `Copula.cdf_ofClassical` recovers `F`. Continuity follows from the
boundary and rectangle conditions. The measure construction uses finite atomic
approximations and weak compactness on the unit cube.

For `θ > 0` and positive coordinates, `Copula.cdf_clayton` proves

```text
Cθ(u) = (∑ i, uᵢ^(-θ) - d + 1)^(-1/θ).
```

A zero coordinate makes the CDF zero. `tendsto_clayton_zero` and
`tendsto_clayton_atTop` give pointwise CDF limits along any filter of positive
parameters. Bivariate Archimedean admissibility is now proved from generator
convexity. `claytonNegative` supplies the bivariate branch `−1 ≤ θ < 0`;
zero is independence. The general higher-dimensional generator criterion
remains outside the current implementation.

The [family catalogue](docs/families.md) lists 27 named families and special
cases, with exact parameter ranges, dimensions, CDF results, and stochastic
constructions. It includes Archimedean, extreme-value, elliptical Gaussian
scale-mixture, polynomial, and mixture families. New Archimedean constructors
are bivariate; the Gaussian scale-mixture constructors support every finite
dimension. The catalogue also records which familiar families remain future work.
See [the design review and roadmap](docs/design.md).

[Vine copulas](docs/vines.md) combine bivariate inputs into C-, D-, and regular
vines in arbitrary dimensions, including singular inputs. `RVineStructure`
specifies variable order and attachment paths, with proved proximity conditions.
`Copula.cVine`, `Copula.dVine`, and `RVineStructure.toCopula` accept measurable
pair families that may depend on the conditioning values. Conditional gluing
preserves both parent marginals at every edge. The direct simplified C-vine
API (`CVine.ofPairs`, `CVine.triple`) also has recursive CDF and independence formulas.

The [Ansari–Rockel coverage index](docs/ansari-rockel.md) covers all 38 distinct
families in *Dependence properties of bivariate copula families*: parameter
domains, CDF/generator/Pickands formulas, dependence and ordering properties,
tails, and every nonempty association-formula entry. It distinguishes checked
Lean results from pending proofs, numerical observations and source discrepancies.
**Full formalization of the paper is not yet complete.**

## Rank dependence

The bivariate API includes Spearman's rho, Kendall's tau, Spearman's footrule,
Gini's gamma, Blomqvist's beta, and Chatterjee's directional xi. All six have
proved range bounds and values at independence, comonotonicity and
countermonotonicity. Xi uses conditional distributions and accepts singular
copulas. See [the definitions, conventions and proved results](docs/rank-coefficients.md).
`Copula.Rank.Region` proves all ten pairwise exact regions among
rho, tau, beta, footrule, and gamma, including boundary witnesses and interior
attainment. See the [exact formulas and proof guide](docs/rank-regions.md).

Xi is proved to vanish exactly at independence and to be strictly convex
under nontrivial mixtures of distinct copulas. Mixing with independence
attenuates xi quadratically. Kendall's tau is proved to equal concordance
probability minus discordance probability for independent observations, and
has general quadratic mixture formulas. FGM, Fréchet and Mardia have proved
closed forms for all six coefficients on their full parameter domains.
Rho, tau and gamma attain ±1 exactly at the corresponding Fréchet copulas.
Footrule attains 1 exactly at comonotonicity; its minimum and beta's extrema
have proved nonuniqueness examples. Rho strictly increases between distinct
copulas comparable in concordance order. Within either PQD or NQD, zero rho
or zero tau characterizes independence.

## Positive dependence

`Copula.Dependence` includes directional LTD, RTI and SI, positive quadrant
dependence, and separate predicates for CDF-TP2, conditional-kernel TP2 and
multivariate density MTP2. It proves implication chains, mixture closure,
rank-coefficient consequences, benchmark examples and exact FGM parameter
classifications. See [the conventions and proved coverage](docs/positive-dependence.md).

## Comparing copulas

`Copula.Order` supplies `LowerOrthantLE`, `UpperOrthantLE`, `ConcordanceLE`,
`SupermodularLE` and directional `SchurLE`. In dimension two, the orthant and
concordance comparisons coincide and preserve all five concordance coefficients.
Schur order preserves Chatterjee's xi; independence is its unique least copula,
while both comonotonicity and countermonotonicity are greatest elements.
See [the ordering conventions, results and remaining work](docs/orders.md).

Further standard results from Nelsen's second edition are indexed in the
[book-to-library coverage map](docs/nelsen.md), including diagonal sections,
symmetries and tail dependence. Tail limits have explicit existence hypotheses;
the library does not silently assign values when limits are unavailable.
For every bivariate extreme-value copula, both limits are proved to exist via
its power diagonal and extremal coefficient. Gumbel, Marshall–Olkin,
Cuadras–Augé and Tawn have explicit tail, footrule and beta formulas,
including singular and independence endpoints.

## Sklar's theorem

For a real-vector probability law `μ`, `Copula.exists_sklarCopula μ` gives a
copula whose CDF composed with the marginal CDFs equals the joint CDF.
This includes atomic and singular laws. The construction uses quantile maps
and randomized inverses, so atoms are handled without assuming the ordinary
CDF transform is uniform.

`Copula.existsUnique_sklarCopula_of_continuous μ hc` gives full uniqueness
when all marginal CDFs are continuous. Strict monotonicity is not required.
Without continuity, `Copula.IsSklarCopula.cdf_eq_on_ranges` asserts equality
on the product of marginal CDF ranges.

## Build

Install [Lean and elan](https://leanprover-community.github.io/get_started.html),
then run:

```sh
git clone https://github.com/Corrram/copula.git
cd copula
lake exe cache get
lake build
lake test
```

The project pins Lean and mathlib to **v4.34.0**. Commit `lake-manifest.json`
when updating dependencies; it fixes the exact transitive revisions. CI builds
both the library and public API examples, with warnings treated as errors.

## Use in another Lean project

Use Lean **v4.34.0** and add the tagged development release to your `lakefile.toml`:

```toml
[[require]]
name = "copula"
git = "https://github.com/Corrram/copula.git"
rev = "v0.1.0"
```

Run `lake update`, then `import Copula.Basic` or `import Copula`. Commit your
dependency manifest to record the exact revisions. Use `rev = "main"` for
ongoing development, or a full commit SHA for a specific snapshot. If you
also declare mathlib directly, use the same mathlib revision as this package.

The GitHub repository is `copula`, the Lake package is `copula`, and the
Lean module root is `Copula`.

### Reservoir

The package enables Reservoir indexing and includes its description, keywords,
version, and Apache-2.0 license in `lakefile.toml`.
[Reservoir indexes eligible GitHub repositories automatically](https://reservoir.lean-lang.org/inclusion-criteria),
approximately daily. Its inclusion criteria require a public, non-fork repository,
a root `lake-manifest.json`, a recognized OSI-approved license, and at least two
GitHub stars. Until indexing completes, use the Git dependency above.

Once the package is indexed, the equivalent Reservoir dependency is:

```toml
[[require]]
name = "copula"
scope = "Corrram"
rev = "v0.1.0"
```

## Feedback and citation

Design questions, API suggestions, and small contributions are welcome through
[GitHub issues](https://github.com/Corrram/copula/issues) and pull requests.
See [CONTRIBUTING.md](CONTRIBUTING.md) for the upstreaming workflow. When linking
from Zulip or a GitHub discussion, prefer a permalink to the relevant commit and
definition. For research citations, use [CITATION.cff](CITATION.cff) and include
the commit SHA; there is no archived release or DOI yet.

Licensed under [Apache 2.0](LICENSE).
