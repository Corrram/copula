# Nelsen Table 4.1: one-parameter Archimedean families

Reference: Roger B. Nelsen, *An Introduction to Copulas*, second edition,
Springer, 2006, Table 4.1 (Section 4.2). The numbering below is Nelsen's and
agrees with the `A01`--`A22` numbering of [Ansari and Rockel](ansari-rockel.md).

Conventions. Nelsen writes `C(u,v) = phi^[-1](phi(u) + phi(v))` with a
decreasing generator `phi`. The library uses the inverse generator `psi`
(field `toFun` of `BivariateGenerator`, convex on `[0, infinity)`) and the
generator `phi` (field `invFun`). Ranges are the ranges of Nelsen's Table 4.1
(as recorded in `docs/ansari-rockel.md`).

Status legend. "in library" means a compiled, proved copula constructor exists.
"new, uncompiled" means the module was written by a process without access to
a Lean toolchain and must be compiled before it is relied on. "missing" means
no Lean constructor exists yet.

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
| 9 | `ln(1 - theta ln t)` | `0 < theta <= 1` | new, uncompiled (whole range) | `Copula.Families.NelsenTable.N9` (`nelsen9`, `cdf_nelsen9`) |
| 10 | `ln(2 t^(-theta) - 1)` | `0 < theta <= 1` | new, uncompiled (full range; inner power of AMH(-1)) | `Copula.Families.NelsenTable.N10` |
| 11 | `ln(2 - t^theta)` | `0 < theta <= 1/2` | missing (non-strict generator with a cutoff at `ln 2`) | |
| 12 | `(1/t - 1)^theta` | `theta >= 1` | in library | `Copula.Families.Nelsen` (`nelsen12`, BB1 with `theta = 1`) |
| 13 | `(1 - ln t)^theta - 1` | `theta > 0` | new, uncompiled for `theta >= 1`; `0 < theta < 1` missing | `Copula.Families.NelsenTable.N13` (`nelsen13`, `cdf_nelsen13`, `nelsen13_one`) |
| 14 | `(t^(-1/theta) - 1)^theta` | `theta >= 1` | in library | `Copula.Families.Nelsen` (`nelsen14`, BB1) |
| 15 | `(1 - t^(1/theta))^theta` | `theta >= 1` | in library (Genest--Ghoudi) | `Copula.Families.Nelsen` (`genestGhoudi`) |
| 16 | `(theta/t + 1)(1 - t)` | `theta >= 0` | missing (inverse generator involves a square root) | |
| 17 | `-ln(((1 + t)^(-theta) - 1)/(2^(-theta) - 1))` | `theta != 0` | missing (not attempted; needs compiler) | |
| 18 | `e^(theta/(t - 1))` | `theta >= 2` | missing (non-strict generator) | |
| 19 | `e^(theta/t) - e^theta` | `theta > 0` | new, uncompiled (whole range) | `Copula.Families.NelsenTable.N19` (`nelsen19`, `cdf_nelsen19`) |
| 20 | `e^(t^(-theta)) - e` | `theta > 0` | new, uncompiled (whole range) | `Copula.Families.NelsenTable.N20` (`nelsen20`, `cdf_nelsen20`) |
| 21 | `1 - (1 - (1 - t)^theta)^(1/theta)` | `theta >= 1` | missing (non-strict generator) | |
| 22 | `arcsin(1 - t^theta)` | `0 < theta <= 1` | missing (non-strict generator, trigonometric inverse) | |

Generic theory for `BivariateGenerator` (diagonal formula, strict inequality
`C(u,u) < u`, generator recovery `phi(psi(s)) = s`) lives in
`Copula.Archimedean.Theory` and `Copula.Archimedean.Diagonal`; shared convexity
lemmas for the new families are in `Copula.Archimedean.TheoryConvex`.
