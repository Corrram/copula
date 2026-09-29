# Nelsen Table 4.1: one-parameter Archimedean families

Reference: Roger B. Nelsen, *An Introduction to Copulas*, second edition,
Springer, 2006, Table 4.1 (Section 4.2). The numbering below is Nelsen's and
agrees with the `A01`--`A22` numbering of [Ansari and Rockel](ansari-rockel.md).

Conventions. Nelsen writes `C(u,v) = phi^[-1](phi(u) + phi(v))` with a
decreasing generator `phi`. The library uses the inverse generator `psi`
(field `toFun` of `BivariateGenerator`, convex on `[0, infinity)`) and the
generator `phi` (field `invFun`). Ranges are the ranges of Nelsen's Table 4.1
(as recorded in `docs/ansari-rockel.md`).

Status legend. "in library" means a compiled, proved copula constructor exists
for the stated range. All 22 families of the table are now in the library, each
on Nelsen's full parameter range (limiting parameter values that are not members
of the family, such as `theta = 0` for #9, are noted where they are proved as
limits or special cases).

| # | Generator `phi(t)` | Range of `theta` | Status | Module and main declarations |
| --- | --- | --- | --- | --- |
| 1 | `(t^(-theta) - 1)/theta` | `theta >= -1`, `theta != 0` | in library (`theta > 0` and `-1 <= theta < 0`; `theta = 0` is independence) | `Copula.Families.Clayton`, `Copula.Archimedean.Clayton` (`claytonGenerator`), `Copula.Families.Clayton.Negative` (`claytonNegative`) |
| 2 | `(1 - t)^theta` | `theta >= 1` | in library | `Copula.Families.Nelsen` (`nelsen2`, `nelsen2_cdf_full`) |
| 3 | `ln((1 - theta(1 - t))/t)` | `-1 <= theta < 1` (the endpoint `theta = 1` is Clayton(1) in this library) | in library | `Copula.Families.AMH` (`amh`, `cdf_amh`) |
| 4 | `(-ln t)^theta` | `theta >= 1` | in library | `Copula.Families.Gumbel` (`gumbel`) |
| 5 | `-ln((e^(-theta t) - 1)/(e^(-theta) - 1))` | `theta != 0` | in library (`theta > 0` and `theta < 0` separately; `theta = 0` is independence) | `Copula.Families.Frank`, `Copula.Families.FrankNegative` |
| 6 | `-ln(1 - (1 - t)^theta)` | `theta >= 1` | in library | `Copula.Families.Joe` (`joe`, `joe_cdf_full`) |
| 7 | `-ln(theta t + (1 - theta))` | `0 < theta <= 1` | in library (also `theta = 0` as W) | `Copula.Families.Nelsen7` (`nelsen7`) |
| 8 | `(1 - t)/(1 + (theta - 1) t)` | `theta >= 1` | in library | `Copula.Families.Nelsen8` (`nelsen8`) |
| 9 | `ln(1 - theta ln t)` | `0 < theta <= 1` | in library (whole range) | `Copula.Families.NelsenTable.N9` (`nelsen9`, `cdf_nelsen9`) |
| 10 | `ln(2 t^(-theta) - 1)` | `0 < theta <= 1` | in library (full range; inner power of AMH(-1)) | `Copula.Families.NelsenTable.N10` (`nelsen10`, `cdf_nelsen10`) |
| 11 | `ln(2 - t^theta)` | `0 < theta <= 1/2` | in library (whole range; non-strict, pseudo-inverse clamped at `ln 2`; `lambda_L = 0`; the limit `Pi` at `theta -> 0` is not formalized) | `Copula.Families.NelsenTable.N11` (`nelsen11`, `cdf_nelsen11`), `Copula.TailDependence.NelsenTable` |
| 12 | `(1/t - 1)^theta` | `theta >= 1` | in library | `Copula.Families.Nelsen` (`nelsen12`, BB1 with `theta = 1`) |
| 13 | `(1 - ln t)^theta - 1` | `theta > 0` | in library (whole range; `theta = 1` is independence) | `Copula.Families.NelsenTable.N13` (`nelsen13`, `cdf_nelsen13`, `nelsen13_one`) |
| 14 | `(t^(-1/theta) - 1)^theta` | `theta >= 1` | in library | `Copula.Families.Nelsen` (`nelsen14`, BB1) |
| 15 | `(1 - t^(1/theta))^theta` | `theta >= 1` | in library (Genest--Ghoudi) | `Copula.Families.Nelsen` (`genestGhoudi`) |
| 16 | `(theta/t + 1)(1 - t)` | `theta >= 0` | in library (whole range; `theta = 0` is `W`; `theta -> infinity` gives `Pi/(Sigma - Pi)` = Clayton(1); `lambda_L = 1/2` for `theta > 0`) | `Copula.Families.NelsenTable.N16` (`nelsen16`, `cdf_nelsen16`, `nelsen16_zero`), `Copula.Families.NelsenTable.Limits` (`tendsto_nelsen16_atTop`), `Copula.TailDependence.NelsenTable` |
| 17 | `-ln(((1 + t)^(-theta) - 1)/(2^(-theta) - 1))` | `theta != 0` | in library (both signs at once; `theta = -1` is independence; the limits `theta -> +-infinity` are not formalized) | `Copula.Families.NelsenTable.N17` (`nelsen17`, `cdf_nelsen17`, `nelsen17_neg_one`) |
| 18 | `e^(theta/(t - 1))` | `theta >= 2` | in library (whole range; non-strict; `theta -> infinity` gives `M`; `lambda_L = 0`, `lambda_U = 1`) | `Copula.Families.NelsenTable.N18` (`nelsen18`, `cdf_nelsen18`), `Copula.Families.NelsenTable.Limits` (`tendsto_nelsen18_atTop`), `Copula.TailDependence.NelsenTable` |
| 19 | `e^(theta/t) - e^theta` | `theta > 0` | in library (whole range) | `Copula.Families.NelsenTable.N19` (`nelsen19`, `cdf_nelsen19`) |
| 20 | `e^(t^(-theta)) - e` | `theta > 0` | in library (whole range) | `Copula.Families.NelsenTable.N20` (`nelsen20`, `cdf_nelsen20`) |
| 21 | `1 - (1 - (1 - t)^theta)^(1/theta)` | `theta >= 1` | in library (whole range; non-strict; `theta = 1` is `W`; `lambda_L = 0`; the limit `M` at infinity is not formalized) | `Copula.Families.NelsenTable.N21` (`nelsen21`, `cdf_nelsen21`, `nelsen21_one`), `Copula.TailDependence.NelsenTable` |
| 22 | `arcsin(1 - t^theta)` | `0 < theta <= 1` | in library (whole range; non-strict; `lambda_L = 0`; corrected CDF, see below; the limit `Pi` at `theta -> 0` is not formalized) | `Copula.Families.NelsenTable.N22` (`nelsen22`, `cdf_nelsen22`), `Copula.TailDependence.NelsenTable` |

Non-strict generators (#11, #18, #21, #22) are built with
`BivariateGenerator.ofClamp` (`Copula.Archimedean.Clamp`): the pseudo-inverse is
`F(min t a)` for the inverse `F` of the generator on `[0, a]`, `a = phi(0)`.
The families whose convexity needs a second-derivative argument (#11, #13,
#17, #18) prove it with `convexOn_of_hasDerivWithinAt2_nonneg`; #16 and #21 use
elementary convexity (Euclidean norm, convex antitone function of a concave
function), and #22 is an inner power of its `theta = 1` member.

Correction for #22. With `a = 1 - u^theta` and `b = 1 - v^theta`, Table 4.1
prints `C(u,v) = max((1 - a sqrt(1 - b^2) - b sqrt(1 - a^2))^(1/theta), 0)`.
This is correct only where `phi(u) + phi(v) <= pi/2`, equivalently
`a^2 + b^2 <= 1`; outside that region the copula is zero while the printed
expression is positive (it tends to one for small `u = v`). `cdf_nelsen22`
states the corrected formula with this case distinction.

Generic theory for `BivariateGenerator` (diagonal formula, strict inequality
`C(u,u) < u`, generator recovery `phi(psi(s)) = s`) lives in
`Copula.Archimedean.Theory` and `Copula.Archimedean.Diagonal`; shared convexity
lemmas for the new families are in `Copula.Archimedean.TheoryConvex`.
