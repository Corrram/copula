# Ansari–Rockel coverage and formula audit

Target: Jonathan Ansari and Marcus Rockel, [*Dependence properties of bivariate
copula families*](https://doi.org/10.1515/demo-2024-0002), Dependence Modeling
12(1), 2024. This index was checked against
[arXiv v3, 6 April 2024](https://arxiv.org/html/2310.17307v3), Tables 1–6 and
Appendix A. It includes **all 38 distinct families**: 22 Archimedean, nine
extreme-value (Gumbel is in both classes), three elliptical and five unclassified.

**This is a reference and a formalization checklist, not a claim that all 38
families or all table entries have Lean proofs.** The `Lean` column identifies
actual measure constructors. `Pending` means there is no constructor yet.
The property and coefficient tables below record mathematical targets; only
declarations linked in the final section are proved in this library. Numerical
observations and unresolved source discrepancies must not become axioms.

## Conventions

- `CI` means SI in both directions; the existing `IsSI` is the paper's CIS.
- `CD` means stochastic decreasingness in both directions.
- The paper's TP2 is **density** TP2 (Definition 2.5), corresponding to
  `HasMTP2Density`, not `IsTP2CDF`. Singular copulas need separate treatment.
- `LO` means `LowerOrthantLE`. The paper's two-direction Schur comparison
  is `SchurBothLE`, requiring both `C.SchurLE D` and
  `C.transpose.SchurLE D.transpose`. `Order.SymmetricSchur` proves that this
  reduces to the directional comparison for exchangeable copulas, in
  particular bivariate Archimedean copulas.
- `↑` and `↓` denote parameter monotonicity. `*` denotes a numerical-only
  observation in the paper. `?` means the paper does not supply a result.
- Formulas are for interior coordinates unless boundary values are explicit.
  Every copula has `C(0,v)=C(u,0)=0`, `C(1,v)=v`, `C(u,1)=u`.
  These must be supplied before using real division, logarithms or negative
  powers in Lean. Limits at parameter endpoints are not substitutions into
  singular expressions.
- Write `P=uv`, `S=u+v`, `W=max(0,S-1)`, `M=min(u,v)`, `x₊=max(0,x)`.
  Let `H=P/(S-P)` on the interior (Clayton at one).

## All families: parameter domains and CDF expressions

### Archimedean families (Tables 1–2)

| ID | Family | Parameters | Interior CDF | Lean |
| --- | --- | --- | --- | --- |
| A01 | Clayton | θ ≥ −1 | `(u^(−θ)+v^(−θ)−1)₊^(−1/θ)` for θ ≠ 0; Π at 0 | `clayton` for θ > 0; `claytonNegative` for −1≤θ<0; `independence 2` at 0 |
| A02 | Nelsen 2 | θ ≥ 1 | `(1−((1−u)^θ+(1−v)^θ)^(1/θ))₊` | `nelsen2` |
| A03 | Ali–Mikhail–Haq | −1 ≤ θ ≤ 1 | `P/(1−θ(1−u)(1−v))` | Pending |
| A04 | Gumbel–Hougaard | θ ≥ 1 | `exp(−((−log u)^θ+(−log v)^θ)^(1/θ))` | `gumbel` |
| A05 | Frank | θ ∈ ℝ | `−log(1+(exp(−θu)−1)(exp(−θv)−1)/(exp(−θ)−1))/θ`; Π at 0 | `frank` for θ > 0 |
| A06 | Joe | θ ≥ 1 | `1−((1−u)^θ+(1−v)^θ−(1−u)^θ(1−v)^θ)^(1/θ)` | `joe` |
| A07 | Nelsen 7 | 0 ≤ θ ≤ 1 | `(θP+(1−θ)(S−1))₊` | `nelsen7` |
| A08 | Nelsen 8 | θ ≥ 1 | `((θ²P−(1−u)(1−v))/(θ²−(θ−1)²(1−u)(1−v)))₊` | Pending |
| A09 | Gumbel–Barnett | 0 ≤ θ ≤ 1 | `P exp(−θ log u log v)` | Pending |
| A10 | Nelsen 10 | 0 ≤ θ ≤ 1 | `P/(1+(1−u^θ)(1−v^θ))^(1/θ)`; Π at 0 | Pending |
| A11 | Nelsen 11 | 0 ≤ θ ≤ 1/2 | `(u^θ v^θ−2(1−u^θ)(1−v^θ))₊^(1/θ)`; Π at 0 | Pending |
| A12 | Nelsen 12 | θ ≥ 1 | `(1+((u^(−1)−1)^θ+(v^(−1)−1)^θ)^(1/θ))^(−1)` | `nelsen12` |
| A13 | Nelsen 13 | θ ≥ 0 | `exp(1−((1−log u)^θ+(1−log v)^θ−1)^(1/θ))`; Gumbel–Barnett at parameter 1 when θ=0 | Pending |
| A14 | Nelsen 14 | θ ≥ 1 | `(1+((u^(−1/θ)−1)^θ+(v^(−1/θ)−1)^θ)^(1/θ))^(−θ)` | `nelsen14` |
| A15 | Genest–Ghoudi (Nelsen 15) | θ ≥ 1 | `(1−((1−u^(1/θ))^θ+(1−v^(1/θ))^θ)^(1/θ))₊^θ` | `genestGhoudi` |
| A16 | Nelsen 16 | θ ≥ 0 | `(s+sqrt(s²+4θ))/2`, `s=S−1−θ(1/u+1/v−1)` | Pending |
| A17 | Nelsen 17 | θ ∈ ℝ, θ ≠ 0 | `(1+((1+u)^(−θ)−1)((1+v)^(−θ)−1)/(2^(−θ)−1))^(−1/θ)−1` | Pending |
| A18 | Nelsen 18 | θ ≥ 2 | `(1+θ/log(exp(θ/(u−1))+exp(θ/(v−1))))₊` | Pending |
| A19 | Nelsen 19 | θ ≥ 0 | `θ/log(exp(θ/u)+exp(θ/v)−exp θ)`; H at 0 | Pending |
| A20 | Nelsen 20 | θ ≥ 0 | `log(exp(u^(−θ))+exp(v^(−θ))−exp 1)^(−1/θ)`; Π at 0 | Pending |
| A21 | Nelsen 21 | θ ≥ 1 | `1−(1−((1−(1−u)^θ)^(1/θ)+(1−(1−v)^θ)^(1/θ)−1)₊^θ)^(1/θ)` | Pending |
| A22 | Nelsen 22 | 0 ≤ θ ≤ 1 | `(1+sin(asin(u^θ−1)+asin(v^θ−1)))^(1/θ)` when the sum of arcsines ≥ −π/2; otherwise 0; Π at θ=0 | Pending |

Generator pairs `(φ,ψ)`, with `C=ψ(φ(u)+φ(v))`. A multiplicative rescaling of
φ and reciprocal rescaling of ψ represent the same copula. These analytic
targets supplement the explicit CDFs above; they are not Lean generators until
their admissibility fields are proved.

| IDs | φ(t) | ψ(y), y ≥ 0 |
| --- | --- | --- |
| A01 | `(t^(−θ)−1)/θ` | `(1+θy)₊^(−1/θ)`; exponential pair at θ=0 |
| A02 | `(1−t)^θ` | `(1−y^(1/θ))₊` |
| A03 | `log((1−θ(1−t))/t)` | `(1−θ)/(exp y−θ)` for θ<1; use H's pair at θ=1 |
| A04 | `(−log t)^θ` | `exp(−y^(1/θ))` |
| A05 | `−log((exp(−θt)−1)/(exp(−θ)−1))` | `−log(1+(exp(−θ)−1)exp(−y))/θ` |
| A06 | `−log(1−(1−t)^θ)` | `1−(1−exp(−y))^(1/θ)` |
| A07 | `−log(1−θ+θt)` | `((exp(−y)+θ−1)/θ)₊`; W at θ=0 |
| A08 | `(1−t)/(1+(θ−1)t)` | `(1−y)₊/(1+(θ−1)y)` |
| A09 | `log(1−θ log t)` | `exp((1−exp y)/θ)`; exponential pair at θ=0 |
| A10 | `log(2t^(−θ)−1)` | `(2/(exp y+1))^(1/θ)`; exponential pair at θ=0 |
| A11 | `log(2−t^θ)` | `(2−exp y)₊^(1/θ)`; exponential pair at θ=0 |
| A12 | `(1/t−1)^θ` | `1/(1+y^(1/θ))` |
| A13 | `(1−log t)^θ−1` | `exp(1−(1+y)^(1/θ))`; scaled limiting pair at θ=0 |
| A14 | `(t^(−1/θ)−1)^θ` | `(1+y^(1/θ))^(−θ)` |
| A15 | `(1−t^(1/θ))^θ` | `(1−y^(1/θ))₊^θ` |
| A16 | `(1−t)(1+θ/t)` | `(1−y−θ+sqrt((1−y−θ)²+4θ))/2` |
| A17 | `−log(((1+t)^(−θ)−1)/(2^(−θ)−1))` | `(1+(2^(−θ)−1)exp(−y))^(−1/θ)−1` |
| A18 | `exp(θ/(t−1))`, φ(1)=0 | `1+θ/log y` for `0<y<exp(−θ)`; 1 at y=0; 0 above cutoff |
| A19 | `exp(θ/t)−exp θ` | `θ/log(y+exp θ)`; H's pair at θ=0 |
| A20 | `exp(t^(−θ))−exp 1` | `log(y+exp 1)^(−1/θ)`; exponential pair at θ=0 |
| A21 | `1−(1−(1−t)^θ)^(1/θ)` | `1−(1−(1−y)^θ)^(1/θ)` for y≤1; 0 otherwise |
| A22 | `−asin(t^θ−1)` | `(1−sin y)^(1/θ)` for y≤π/2; 0 otherwise; exponential pair at θ=0 |

### Extreme-value families (Tables 1 and 4)

Their common interior expression is
`C(u,v)=exp((log u+log v) A(log v/(log u+log v)))`.
The following gives a closed Pickands expression for every EV row, including
the Gumbel overlap. At t=0 or t=1 set A(t)=1; powers with zero bases and negative
exponents require limits. `Φ` is the standard normal CDF and `Tν` the Student-t CDF.

| ID | Family | Parameters | A(t) | Lean |
| --- | --- | --- | --- | --- |
| E01 | BB5 | θ≥1, δ>0 | `(t^θ+(1−t)^θ−((1−t)^(−θδ)+t^(−θδ))^(−1/δ))^(1/θ)` | Pending |
| E02 | Cuadras–Augé | 0≤δ≤1 | `1−δ min(t,1−t)` | `cuadrasAuge` |
| E03 | Galambos | δ>0 | `1−(t^(−δ)+(1−t)^(−δ))^(−1/δ)` | Pending |
| A04 | Gumbel–Hougaard | θ≥1 | `(t^θ+(1−t)^θ)^(1/θ)` | `gumbel` |
| E04 | Hüsler–Reiss | δ≥0 | `(1−t)Φ(z(1−t))+tΦ(z(t))`, `z(t)=1/δ+(δ/2)log(t/(1−t))`; A=1 at δ=0 | Pending |
| E05 | Joe EV | α,β∈[0,1], δ>0 | `1−((α(1−t))^(−δ)+(βt)^(−δ))^(−1/δ)`; A=1 if αβ=0 | Pending |
| E06 | Marshall–Olkin | α,β∈[0,1] | `max(1−α(1−t),1−βt)` | `marshallOlkin` |
| E07 | Tawn | α,β∈[0,1], θ≥1 | `(1−α)(1−t)+(1−β)t+((α(1−t))^θ+(βt)^θ)^(1/θ)` | `tawn` |
| E08 | t-EV | −1<r<1, ν>0 | `(1−t)T(ν+1,z(1−t))+tT(ν+1,z(t))`, `z(t)=sqrt((1+ν)/(1−r²))((t/(1−t))^(1/ν)−r)` | Pending |

Special/limiting cases to retain: BB5 at θ=1 is Galambos and as δ→0 is
Gumbel; Galambos and Hüsler–Reiss range from Π to M; Joe EV at α=β=1 is
Galambos and as δ→∞ tends to Marshall–Olkin; Tawn at α=β=1 is Gumbel
and as θ→∞ tends to Marshall–Olkin. The named `gumbel_cdf_full`, `tawn_cdf_positive`, and `tawn_cdf_full`
formulas are checked, including the grounded zero axes. The finite-parameter
identities `tawn_one_one`, `tawn_zero_left`, `tawn_zero_right`, and `tawn_shape_one`
are proved, including every endpoint. The infinite-parameter limit still
requires proof; it is not evaluation at an infinite real parameter. The t-EV limiting-case column
of Table 4 requires independent checking (see source audit below).

### Elliptical and unclassified families (Tables 1 and 4)

For an elliptical bivariate law with joint CDF F and common continuous margin G,
the expression is `C(u,v)=F(G⁻¹(u),G⁻¹(v))`. This is an exact distributional
expression, not generally an elementary closed form. The existing constructors
prove its Sklar interpretation for Gaussian scale mixtures.

| ID | Family | Parameters | CDF / defining law | Lean |
| --- | --- | --- | --- | --- |
| L01 | Gaussian | −1≤r≤1 | Bivariate standard normal, correlation r; W and M at −1 and 1 | `gaussian` |
| L02 | Student-t | −1≤r≤1, ν>0 | `Z/sqrt(G)`, `G~Gamma(ν/2,rate ν/2)` independent of correlated normal Z | `studentT` |
| L03 | Laplace | −1≤r≤1 | `sqrt(G) Z`, `G~Exp(1)` independent of correlated normal Z | `laplace` |
| U01 | Fréchet | α,β≥0, α+β≤1 | `αM+βW+(1−α−β)P` | `frechet` |
| U02 | Mardia | −1≤θ≤1 | Fréchet with `α=θ²(1+θ)/2`, `β=θ²(1−θ)/2` | `mardia` |
| U03 | FGM | −1≤θ≤1 | `P(1+θ(1−u)(1−v))` | `fgm` |
| U04 | Plackett | θ>0 | `(1+(θ−1)S−sqrt((1+(θ−1)S)²−4Pθ(θ−1)))/(2(θ−1))`; Π at 1 | Pending |
| U05 | Raftery | 0≤δ≤1 | `M+(1−δ)/(1+δ) P^(1/(1−δ))(1−max(u,v)^(−(1+δ)/(1−δ)))`; M at δ=1 | Pending |

The Raftery expression includes the normalization missing in v3 Table 1;
see [Schmidt's copula table](https://wisostat.uni-koeln.de/fileadmin/sites/statistik/pdf_publikationen/TDCSchmidt.pdf),
and the paper's own conditional derivative (25). For L02, the bivariate density
has exponent `−(ν+2)/2`; the correlation parameter is not the dimension.

For nonsingular elliptical parameters, the joint CDF above is the double
integral of the following density over `(-∞,x] × (-∞,y]`. Write
`q=(x²−2rxy+y²)/(1−r²)`:

- Gaussian: `exp(−q/2)/(2π sqrt(1−r²))`.
- Student-t: `Γ((ν+2)/2)/(Γ(ν/2) νπ sqrt(1−r²)) · (1+q/ν)^(−(ν+2)/2)`.
- Laplace: `K₀(sqrt(2q))/(π sqrt(1−r²))`, with K₀ the modified Bessel
  function. For the scale-mixture normalization used here the univariate
  Laplace scale is `1/sqrt 2`; changing that common scale leaves the copula
  unchanged. The density's value at the origin is immaterial to its measure.

These distributional density expressions are reference formulas; their
identification with the existing Lean measures remains pending.

## Dependence, ordering and tails: every family

This is a target index of Tables 3 and 5, with endpoint cautions. No unlinked
cell is a declaration of a proved Lean result. `split(c)` means LO increases,
Schur decreases below c and increases above c. Tail pairs are `(λL,λU)`.

| ID | CI / CD region | Density TP2 | LO; Schur | Tail pair / caveat |
| --- | --- | --- | --- | --- |
| A01 | CI θ≥0; CD θ≤0 | θ≥0 | split(0) | `(2^(−1/θ),0)` for θ>0; `(0,0)` for θ≤0 |
| A02 | neither for θ>1; CD at 1 | no | ↑; unordered* | `(0,2−2^(1/θ))` |
| A03 | CI θ≥0; CD θ≤0 | θ≥0 | split(0) | `(0,0)` for θ<1; `(1/2,0)` at 1 |
| A04 | CI | yes | ↑; ↑ | `(0,2−2^(1/θ))` |
| A05 | CI θ≥0; CD θ≤0 | θ≥0 | split(0) | `(0,0)` |
| A06 | CI | yes | ↑; ↑ | `(0,2−2^(1/θ))` |
| A07 | CD; also CI at 1 | only θ=1 | ↑; ↓ | `(0,0)` |
| A08 | neither for θ>1; CD at 1 | no | ↑; unordered* | `(0,0)` |
| A09 | CD; also CI at 0 | only θ=0 | ↓; ↑ | `(0,0)` |
| A10 | CD; also CI at 0 | only θ=0 | unordered; unordered | `(0,0)` |
| A11 | CD; also CI at 0 | only θ=0 | ↓; ↑ | `(0,0)` |
| A12 | CI | yes | ↑; ↑ | `(2^(−1/θ),2−2^(1/θ))` |
| A13 | CI iff θ≥1 | iff θ≥1 | ↑; ↑ on θ≥1 | `(0,0)` |
| A14 | CI | yes | ↑; ↑ | `(1/2,2−2^(1/θ))` |
| A15 | neither for θ>1; CD at 1 | no | ↑; unordered* | `(0,2−2^(1/θ))` |
| A16 | CI iff θ≥3 | iff θ≥3+2sqrt 2 | ↑; ↑ on θ≥3 | `(1/2,0)` for θ>0; `(0,0)` at 0 |
| A17 | CI θ≥−1; CD θ≤−1 | iff θ≥−1 | split(−1), excluding θ=0 | `(0,0)` |
| A18 | neither | no | ↑; unordered* | `(0,1)` |
| A19 | CI | yes | ↑; ↑ | `(1,0)` for θ>0; `(1/2,0)` at 0 |
| A20 | CI | yes | ↑; ↑ | `(1,0)` for θ>0; `(0,0)` at 0 |
| A21 | neither for θ>1; CD at 1 | no | ↑; unordered* | `(0,2−2^(1/θ))` |
| A22 | CD; also CI at 0 | only θ=0 | ↓; ↑ | `(0,0)` |
| E01 | CI | ? | ↑ in δ; ↑ in δ | `(0,2−(2−2^(−1/δ))^(1/θ))` |
| E02 | CI | only δ=0 | ↑; ↑ | `(1{δ=1},δ)` |
| E03 | CI | ? | ↑; ↑ | `(0,2^(−1/δ))` |
| E04 | CI | yes* | ↑; ↑ | `(0,2(1−Φ(1/δ)))` for δ>0; `(0,0)` at 0 |
| E05 | CI | no* away from Π | ↑ in δ; ↑ in δ | `(0,(α^(−δ)+β^(−δ))^(−1/δ))`; upper 0 if αβ=0 |
| E06 | CI | no if αβ>0; Π if αβ=0 | ↑ on α=β; ↑ on α=β | `(1{α=β=1},min(α,β))` |
| E07 | CI | no* away from Π; audit Gumbel subfamily | ↑ in θ; ↑ in θ | `(0,α+β−(α^θ+β^θ)^(1/θ))` |
| E08 | CI | no* | ↑ in r; ↑ in r | `(0,2(1−T(ν+1,sqrt((ν+1)(1−r)/(1+r)))))` |
| L01 | CI r≥0; CD r≤0 | 0≤r<1; singular at ±1 | split(0) | `(0,0)` for r<1; `(1,1)` at 1 |
| L02 | neither for −1<r<1 | no | ↑ in r; ? | both `2(1−T(ν+1,sqrt((ν+1)(1−r)/(1+r))))`; limits 0 at −1 and 1 at 1 |
| L03 | paper excludes CI for r≤0 in interior; rest ? | no in interior | ↑ in r; ? | ? in interior; W/M endpoints give 0/1 |
| U01 | CI iff β=0; CD iff α=0 | source cell inconsistent with density definition | ↑ in α, **↓** in β; Schur ↑ on each unmixed axis | `(α,α)` |
| U02 | CI at 0,1; CD at −1,0 | source cell omits Π and includes singular M | unordered; Schur ↑ for θ≥0*, ↓ for θ≤0* | both `θ²(1+θ)/2` |
| U03 | CI θ≥0; CD θ≤0 | θ≥0 | split(0) | `(0,0)` |
| U04 | CI θ≥1; CD θ≤1 | no for θ>2; yes on [1,2]*; no for θ<1 | split(1); printed Schur range needs audit | `(0,0)` |
| U05 | CI | only δ=0 | ↑; ↑ | `(2δ/(1+δ),0)` for δ<1; `(1,1)` at 1 |

LTD, RTI and PQD follow from SI where the library's implication theorems
apply. They should be derived once from the relevant CI/CIS proof rather
than inserted as independent assumptions in every family record.

## Association expressions (all nonempty cells of Table 6)

Blank cells in the paper mean **no expression supplied there**, not zero.
Let `Dk(x)=k/x^k ∫₀ˣ t^k/(exp t−1) dt`,
`E1(x)=∫₁∞ exp(−xs)/s ds`, and let `₂F₁` denote the hypergeometric function.
ξ is directional: second coordinate given first.

| ID | ξ | Spearman ρ | Kendall τ |
| --- | --- | --- | --- |
| A01 | `6∫₀¹ ₂F₁(1/θ,2+2/θ;1+1/θ;1−v^(−θ)) dv−2`, θ>0 | not supplied | `θ/(θ+2)` |
| A03 | `3/θ−θ/6−2/3−2/θ²−2(θ−1)²log(1−θ)/θ³` | `12(1+θ)/θ² ∫₁^(1−θ) log t/(1−t) dt−24(1−θ)log(1−θ)/θ²−3(θ+12)/θ` | `1−2/(3θ)−2(1−θ)²log(1−θ)/(3θ²)` |
| A05 | not supplied | `1−12(D1(θ)−D2(θ))/θ` | `1−4(1−D1(θ))/θ` |
| A07 | `1−θ` | `(9θ²−6θ−6(θ−1)²log(1−θ))/θ³−3` | `2(θ²−θ−(θ−1)²log(1−θ))/θ²` |
| A09 | `3 exp(3/(2θ)) E1(3/(2θ))/(4θ)+θ/3−1/2` | not supplied | not supplied |
| E02 | `δ²/(2−δ)` | `3δ/(4−δ)` | `δ/(2−δ)` |
| A04 | not supplied | `12/θ ∫₀¹ (t(1−t))^(1/θ−1)/(1+t^(1/θ)+(1−t)^(1/θ))² dt−3` | `(θ−1)/θ` |
| E06 | `2α²β/(3α+β−2αβ)` | `3αβ/(2α−αβ+2β)` | `αβ/(α−αβ+β)` |
| L01 | printed `3/π asin(1/2+r²/(1+r))−1/2` **requires correction** | `6 asin(r/2)/π` | `2 asin r/π` |
| L02 | not supplied | `6 E[asin(r Ṽ₁)]/π` | `2 asin r/π` |
| L03 | not supplied | `6 E[asin(r Ṽ₂)]/π` | `2 asin r/π` |
| U01 | `(α−β)²+αβ` | `α−β` | `(α−β)(α+β+2)/3` |
| U02 | `θ⁴(3θ²+1)/4` | `θ³` | `θ³(θ²+2)/3` |
| U03 | `θ²/15` | `θ/3` | `2θ/9` |
| U04 | not supplied | printed `(θ+1)/(θ−1)−4θ log θ/(θ−1)²` **requires correction** | not supplied |
| U05 | not supplied | `δ(4−3δ)/(2−δ)²` | `2δ/(3−δ)` |

The mixing laws of Ṽ₁ and Ṽ₂ must be specified as in Heinen–Valdesogo,
Proposition 1, before implementing those expectations. The displayed expression
alone does not define the random variables. Special functions and integrals
in this table must not be advertised as elementary formulas.

Removable cases: AMH and Frank at zero give all three coefficients zero;
Nelsen 7 at zero gives `(ξ,ρ,τ)=(1,−1,−1)` and at one gives `(0,0,0)`;
Gumbel–Barnett at zero gives ξ=0; Marshall–Olkin with a zero weight gives
all three zero; Plackett at one gives ρ=0. Endpoints with logarithms require
limit proofs. Footrule, gamma and beta are additional library targets, not
columns supplied by this paper.

## Source audit: do not silently transcribe these cells

These observations concern the version linked above, not a claim about every
published version. Corrections below are mathematical checks against definitions
and special cases, not a published erratum.

1. Gaussian tails at r=−1 must be zero: that copula is W. Table 5 and A.3.3
   incorrectly include this endpoint with M. The library already proves W's
   two tail limits are zero.
2. The printed Gaussian ξ expression is not even in r, is singular at −1,
   and has an arcsine argument above one for some negative r. The expression
   to verify from the cited source is `3 asin((1+r²)/2)/π−1/2`.
3. The printed Plackett ρ has an extra factor two on its logarithmic term;
   it fails the independence limit at θ=1. The target to verify is
   `(θ+1)/(θ−1)−2θ log θ/(θ−1)²`.
4. Fréchet LO decreases in β: increasing the weight of W replaces Π by W≤Π.
   Table 5/A.4.2 say increasing in both weights. A.4.1 also reverses the
   simplex inequality, and equation (23) gives the wrong sign for Mardia's β.
5. Density TP2 cannot include M: it has no Lebesgue density. The Fréchet and
   Mardia TP2 cells conflict with Definition 2.5 and also omit independence.
6. Mardia at θ=0 is Π, hence both CI and CD. The printed CI/CD cells omit it.
7. AMH at θ=1 is H and has lower tail coefficient 1/2, not zero. Its printed
   generator degenerates at one and must be replaced by H's generator.
8. Nelsen 16 at zero is W, Nelsen 19 at zero is H, and Nelsen 20 at zero is Π.
   Their lower-tail entries therefore need separate endpoints (0, 1/2, 0).
9. Nelsen 18's inverse-generator cutoff in Table 2 has its inequality reversed.
   Nelsen 21's cutoff must be one, not π/2.
10. Tawn's Pickands term must be `(α(1−t))^θ`, with α inside the power.
    Its numerical non-TP2 claim cannot apply to α=β=1, the Gumbel subfamily.
    Joe EV's analogous claim must also respect its Galambos subfamily.
11. The second Marshall–Olkin TP2 row cannot exclude α>0, β=0: this is Π.
    Singular endpoints must be handled independently of density arguments.
12. Raftery's CDF needs the factor `1/(1+δ)`. Its upper-tail coefficient is
    zero for δ<1 but equals one at δ=1, where the copula is M.
13. Table 1's Student-t density uses the correlation symbol where the dimension
    two is needed. The t-EV limits in Table 4 also need checking: the displayed
    Marshall–Olkin parameter can lie outside [0,1], and a Hüsler–Reiss limit
    requires an appropriate joint parameter regime.
14. Plackett's negative-side Schur interval ends at one, not zero; θ>0 is its
    parameter domain. The numerical TP2 observation on [1,2] remains numerical.

## Checked implementation and remaining work

The four added families A02, A12, A14 and A15 have measure constructors,
Archimedean classification, exact interior CDF theorems and endpoint
identifications in [Nelsen.lean](../Copula/Families/Nelsen.lean).
[Truncated.lean](../Copula/Archimedean/Truncated.lean) proves the non-strict
linear generator; [Power.lean](../Copula/Archimedean/Power.lean) proves both
generator power transformations. These are genuine validity proofs in dimension
two, including singular distributions, without density assumptions.

[Nelsen7.lean](../Copula/Families/Nelsen7.lean) adds A07 with its CDF on the
entire square, CD, increasing LO order and both endpoints. The general density-PQD bridge in [Dependence/DensityTotalPositivity.lean](../Copula/Dependence/DensityTotalPositivity.lean) also gives both exact total-positivity ranges: only θ=1 (independence) has a TP2 CDF or admits an MTP2 density. The
[negative Clayton branch](../Copula/Families/Clayton/Negative.lean) covers
−1≤θ<0 and identifies −1 with W. The library now has constructors for 18 of
the paper's 38 families; Frank still has only its positive branch. A constructor
count is not a count of fully proved property tables.

[Dependence/Clayton.lean](../Copula/Dependence/Clayton.lean) proves CI (in both directions) and positive quadrant dependence for every positive Clayton parameter, and negative quadrant dependence throughout −1≤θ<0. The positive-parameter CI proof uses concavity of every first-coordinate CDF section and Archimedean symmetry. The negative-parameter CD entry is proved in [Dependence/ClaytonNegative.lean](../Copula/Dependence/ClaytonNegative.lean) by a convex-section argument across the truncated support. [Dependence/ClaytonClassification.lean](../Copula/Dependence/ClaytonClassification.lean) proves the reverse exclusions by strict midpoint quadrant comparisons, completing the signed CI/CD parameter split. [TailDependence/Clayton.lean](../Copula/TailDependence/Clayton.lean) proves both exact tail coefficients for each signed branch: `(2^(−1/θ),0)` for θ>0 and `(0,0)` for −1≤θ<0. The exact CDF-level TP2 region is now checked separately in [Dependence/ClaytonTotalPositivity.lean](../Copula/Dependence/ClaytonTotalPositivity.lean): every θ>0 has a TP2 CDF, θ=0 is independence and has a TP2 CDF, while every −1≤θ<0 fails CDF TP2. The θ=−1 endpoint is W and has no Lebesgue MTP2 density. [Dependence/ClaytonDensityFormula.lean](../Copula/Dependence/ClaytonDensityFormula.lean) also checks MTP2 of the standard positive-parameter density formula as a function. [Dependence/ClaytonDensityMeasure.lean](../Copula/Dependence/ClaytonDensityMeasure.lean) identifies that formula with the actual Clayton measure on the full square. Consequently every θ>0 has an actual MTP2 density and is absolutely continuous. [Dependence/DensityTotalPositivity.lean](../Copula/Dependence/DensityTotalPositivity.lean) proves that any copula with an MTP2 density is PQD, then uses strict non-PQD of negative Clayton to exclude all −1≤θ<0. Thus the signed Clayton density-TP2 range is exactly θ≥0, including the independence parameter.

[ConditionalMonotonicity.lean](../Copula/Dependence/ConditionalMonotonicity.lean)
defines CI/CD, proves reflection duality and exact FGM CI/CD regions.
[FGMKendall.lean](../Copula/Rank/FGMKendall.lean) proves τ=2θ/9;
[FGMChatterjee.lean](../Copula/Rank/FGMChatterjee.lean) identifies the
conditional CDF and proves ξ=θ²/15, completing FGM's three Table 6 entries
and all six library rank coefficients.
[Rank/Frechet.lean](../Copula/Rank/Frechet.lean) proves ρ=α−β and ρ=θ³.
[Order/Frechet.lean](../Copula/Order/Frechet.lean) proves the corrected weight
ordering and a counterexample to the reversed claim.
[FGMSchur.lean](../Copula/Order/FGMSchur.lean) proves FGM Schur order in
either or both directions exactly when the absolute parameters are ordered.

Previously proved family results are indexed in [families](families.md),
[positive dependence](positive-dependence.md), [orders](orders.md),
[rank coefficients](rank-coefficients.md), and [tail dependence](nelsen.md).
In particular FGM has exact parameter classification, LO order, an actual
MTP2 density exactly for nonnegative parameters, rho/footrule/gamma/beta
formulas and both zero tails. The negative exclusion covers every possible
density version via the general CD-plus-MTP2 independence theorem. Fréchet and Mardia have
both tail formulas. These facts do not establish the remaining table cells.

[ExtremeValue/Diagonal.lean](../Copula/ExtremeValue/Diagonal.lean) proves
the power diagonal and extremal coefficient for every bivariate max-stable
copula. [TailDependence/ExtremeValue.lean](../Copula/TailDependence/ExtremeValue.lean)
now checks both tail formulas for A04 (Gumbel), E02 (Cuadras–Augé), E06
(Marshall–Olkin) and E07 (Tawn). Lower tails at the `M` endpoints are one;
the other parameters have lower tail zero. These include all admitted zero
weights and `θ=1` cases. [Rank/PowerDiagonal.lean](../Copula/Rank/PowerDiagonal.lean)
also proves their footrule and beta formulas, which supplement the paper's
rho/tau/xi table rather than completing its outstanding entries.

[Rank/FrechetChatterjee.lean](../Copula/Rank/FrechetChatterjee.lean) now proves
the Table 6 xi formulas for U01 and U02: `(α−β)²+αβ` and
`θ⁴(1+3θ²)/4`, including the entire simplex and both signed Mardia endpoints.
[Rank/FrechetKendall.lean](../Copula/Rank/FrechetKendall.lean) proves their tau
formulas `(α−β)(α+β+2)/3` and `θ³(θ²+2)/3`, completing the rho/tau/xi entries
for both families in Table 6. It also proves footrule, gamma and beta, so all
six library coefficients now have formulas for U01 and U02. The shared
[Kendall mixture API](../Copula/Rank/KendallMixture.lean) expresses tau as a
quadratic form in the weights, with cross terms given by the concordance
function Q; its [probability interpretation](../Copula/Rank/ConcordanceProbability.lean)
is proved for arbitrary bivariate copulas, including singular ones.
The shared [mixture API](../Copula/Rank/ChatterjeeMixture.lean) proves exact
quadratic identities and strict convexity of xi. The
[conditional-distance API](../Copula/Rank/ConditionalDistance.lean) proves
xi=0 iff independence for every bivariate copula, including singular laws.

[Dependence/Frechet.lean](../Copula/Dependence/Frechet.lean) now proves exact
CI/CD classifications and absolute continuity/density TP2 for U01 and U02,
including independence and singular endpoints. Frechet is CI iff b=0 and CD
iff a=0; Mardia is CI at theta=0,1 and CD at theta=-1,0. Both families have a
Lebesgue density exactly at independence, which is also their exact density-TP2
region. These correct the printed singular-endpoint TP2 and omitted independence
claims; they do not classify alternative total-positivity notions.

[Rank/Nelsen7.lean](../Copula/Rank/Nelsen7.lean) identifies the conditional CDF
and proves A07's Table 6 formula xi=1-theta on the entire closed interval.
[Order/Nelsen7.lean](../Copula/Order/Nelsen7.lean) proves the exact Schur order
in both directions: C_theta precedes C_eta iff eta<=theta. The family is
CI exactly at independence (theta=1), while CD holds throughout.
The full Nelsen 7 rho and tau expressions are proved in [Rank/Nelsen7Rho.lean](../Copula/Rank/Nelsen7Rho.lean) and [Rank/Nelsen7Tau.lean](../Copula/Rank/Nelsen7Tau.lean), including both endpoint values. The density-TP2 entry remains a separate obligation.

Outstanding proof work includes the other named constructors, full signed
Frank, generator criteria for CI/CD and density TP2, Pickands representation
and admissibility, the CI/CD equivalences between LO and Schur order,
family parameter orders, analytic tail limits, and the unproved coefficient
formulas above. A family is complete only after its domain, boundary cases,
CDF, applicable property/order statements and supplied coefficient expressions
are linked to checked declarations. Unknown and numerical-only source cells
remain separately identified even when the rest of their family is formalized.
